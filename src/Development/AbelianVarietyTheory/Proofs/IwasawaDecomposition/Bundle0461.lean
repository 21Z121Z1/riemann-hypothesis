import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.Columns.Bundle0064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionUnfolded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Formalism.LocalToGlobal.KernelLattices.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationFormLatticeIffClassValuesWeylLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspValues

theorem evEx_of_range {K C H X : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup X] [Module ℂ X] (σ : K →+* ℂ) (ev : H →ₗ[ℂ] X) (hinj : Function.Injective ev) (φ : C →ₛₗ[σ] X)
    (h : ∀ f, φ f ∈ LinearMap.range ev) : EvEx σ ev φ := by
  choose x hx using h
  refine ⟨⟨⟨x, fun f f' => hinj ?_⟩, fun a f => hinj ?_⟩, hx⟩
  · rw [map_add, hx, hx, hx, map_add]
  · exact (hx _).trans (by rw [φ.map_smulₛₗ, map_smul, hx])

theorem phiC_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T hV a f = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
        (rdU (T.U j σ) f) := by
  subst hV
  rfl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

noncomputable def evLin {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' a b := by simp [evAt]
  map_smul' c a := by simp [evAt]

set_option maxHeartbeats 1000000 in

theorem jEvExists (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (ht : TieIn T R κ v₀) (hp : T.pb = R.C.P.pb) : JEvExists T R κ v₀ := by
  intro i σ hσ hV
  obtain ⟨hsh, -, w, hw⟩ := GlobalTheory.T.holomorphicShape_integralWeight_goodEmbedding D G Pl0 T0 A T R κ v₀ ht i σ hσ
  have hg := GlobalTheory.T.coreDictionary_good_at_good_embedding D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV w hw
  obtain ⟨-, hχ, hfin, -⟩ := GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV
  have hinj : Function.Injective (evLin R i σ (v₀ i σ)) :=
    GlobalTheory.EvalAtUnitVector.evInj T R v₀ hM.HW ht.hv₀ i σ hσ
  let ad := adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ)))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ)))
      (T.cE ((i : ℕ) + 1) (res T σ)))
  have key : holSub (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) ≤
      (LinearMap.range (evLin R i σ (v₀ i σ))).comap ad := by
    refine Submodule.span_le.2 fun P hP => ?_
    have h1 := GlobalTheory.T.holomorphicAdelicForm_of_boundedSection D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hsh hg P fun k => (hP k).1
    have h2 := GlobalTheory.T.adelicCuspForm_transvection_constantTerms_zero D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hsh hg P hP
    have h3 : GlobalTheory.HolDict.HolForm R.θ (R.MW i σ) w (levS _ (R.βW i) (R.datWp i R.triv))
        (Lev.levChi _ (R.βW i) (R.datWp i R.triv)) (ad P) :=
      ⟨h1.aut, h1.bdd, fun k hk g => by rw [hχ k hk]; exact h1.lev k hk g, h1.hol⟩
    obtain ⟨Tm, hT, hTv⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D R.θ _ _ (R.MW i σ) w (v₀ i σ) hM.inf hsh hw (ht.hv₀ i σ).1
      (GlobalTheory.HolDict.exists_finPair GlobalTheory.Mem.VolFin.finVol D _) _ _ _ hfin h3 h2
    have hmem : Tm ∈ R.Wall i σ := Submodule.subset_span hT
    rw [← (hM.HW i σ).2.1] at hmem
    obtain ⟨x, rfl⟩ := hmem
    exact ⟨x, hTv⟩
  let φ : Cu T κ i →ₛₗ[res T σ] (GA D (Wc D i) → ℂ) :=
    ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) • ad).comp
      ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype)
  have h := evEx_of_range (res T σ) _ hinj φ fun f =>
    Submodule.smul_mem _ _ (key (((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hσ))
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun f => (hj f).trans (phiC_eq T hV _ _).symm⟩

theorem jEvExists_and_jEvBar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hp
  have h := jEvExists T R κ v₀ hL hM ht hp
  exact ⟨h, (GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM ht).2 h⟩

end GlobalTheory.CuspValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem memSideU_std {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hP : TC.Pins B X) (hS : I.StdKer l Z t) (hpi : ex.errX.piT = X.piT) : t.MemSideU := by
  intro u
  refine ⟨?_, ?_, ?_⟩
  · show (t.O u I.mu0).mt = _
    rw [hS.O.mt u I.mu0, hOk.trueColumnChoices_heckeChar_reference_eq_one, tildeQ_one]
    funext j
    split_ifs
    · exact mul_one _
    · rfl
  · intro i c
    show (t.O u I.mu0).dt i c = _
    rw [hS.O.dt u I.mu0 i c]
    rfl
  · rw [hpi]
    exact memLatAt_std I hOk hP l Z u (t.memObj u) fun i c => hS.O.lat u I.mu0 i c

theorem piSide_std {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hS : I.StdKer l Z t) (hpi : ex.errX.piT = X.piT) : t.PiSide := by
  obtain ⟨hX, hseam, hPr, -, -, -, hword, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  cases hseam
  cases hPr
  cases hword
  intro u
  rw [hpi]
  rfl

theorem chOk_std {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hS : I.StdKer l Z t) : t.Ch.Ok ∧ MuValTie t.Ch t.glob ∧ ∀ a, (t.cst a).sharp = true := by
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hglob
  exact ⟨hOk.ch_ok, fun j v h => hOk.ch_tied.muVal j v h, fun a => hOk.sharp a⟩

theorem k_pins_of_fields {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hP : TC.Pins B X)
    (hX : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hSS : t.S = I.S) (hword : HEq t.word fun u : B.Word => u)
    (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst) (hglob : HEq t.glob I.glob) (hO : I.StdO l Z Y.Qp t.O)
    (hpi : ex.errX.piT = X.piT) : t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  have hU : t.MemSideU := by
    intro u
    refine ⟨?_, ?_, ?_⟩
    · show (t.O u I.mu0).mt = _
      rw [hO.mt u I.mu0, hOk.trueColumnChoices_heckeChar_reference_eq_one, tildeQ_one]
      funext j
      split_ifs
      · exact mul_one _
      · rfl
    · intro i c
      show (t.O u I.mu0).dt i c = _
      rw [hO.dt u I.mu0 i c]
      rfl
    · rw [hpi]
      exact memLatAt_std I hOk hP l Z u (t.memObj u) fun i c => hO.lat u I.mu0 i c
  have hPi : t.PiSide := by
    clear hU hO hglob hcst htup hSS hsel hCh
    cases t
    dsimp only at *
    subst hX
    cases hseam
    cases hPr
    cases hword
    intro u
    rw [hpi]
    rfl
  have hC : t.Ch.Ok ∧ MuValTie t.Ch t.glob ∧ ∀ a, (t.cst a).sharp = true := by
    clear hU hPi
    cases t
    dsimp only at *
    subst hX
    cases hPr
    cases hCh
    cases hsel
    subst hSS
    cases htup
    cases hcst
    cases hglob
    exact ⟨hOk.ch_ok, fun j v h => hOk.ch_tied.muVal j v h, fun a => hOk.sharp a⟩
  have hM : t.MtTwTie := by
    clear hU hPi hC
    cases t
    dsimp only at *
    subst hX
    cases hseam
    subst hSS
    cases htup
    refine ⟨(QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)), ⟨fun y => ?_, fun k z hz => ?_⟩,
      fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
      refine ⟨finAf B.host.F B.host.E a, ?_⟩
      exact mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)
    · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
      show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
      rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
      refine mk_eq_of_snd_eq B.host I.SQ ?_
      show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
      rw [afIso_tmul_one]
      rfl
    · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
        (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).2.2 μ).1
      show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
      exact Units.ext ((hOk.xi_reads μ).apply _ x rfl)
    · rw [hO.mt u μ]
      rfl
  exact ⟨⟨hC.1, hC.2.1, hPi, fun u _ => hU u⟩, hU, hM, hC.2.2⟩

theorem k_pins_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS hpi
  exact k_pins_of_fields I l Z t hOk hP hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.word hS.tup hS.cst hS.glob hS.O hpi

theorem k_pins : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS hpi
  have hU := memSideU_std I l Z t hOk hP hS hpi
  obtain ⟨h1, h2, h3⟩ := chOk_std I l Z t hOk hS
  exact ⟨⟨h1, h2, piSide_std I l Z t hS hpi, fun u _ => hU u⟩, hU, mtTwTie_std I hOk l Z L hT Gi Gl K Y cX ex t hS, h3⟩

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open Formalism.HermitianLatticesTheory

theorem topChain : TopChain := by
  classical
  intro D X u C r Pr Ch sel S mu cst L σ v m2 hX hPr hc hm hpi h
  obtain ⟨hSS, hlev, pt, ix, yb, pT, hN, hyb, hE, hC, ⟨hTN, hTX⟩, hpin, hpin'⟩ := h
  have key : ∀ (c' : C.cls (m2 + 1 + 1)) d, OverRow sel mu v d (pT c') →
      HEq (r.N (m2 + 1 + 1) c') (tilQ sel mu v d).1.N ∧ ∀ c, HEq (r.Xi (m2 + 1) c c') fun x => σ (XiCpl2 Ch sel mu cst m2 (pt (m2 + 1) le_rfl c) (yb c) d x) := by
    intro c' d hd
    obtain ⟨p', hp, hrow⟩ := hd
    have gen : ∀ (j : ℕ) (hj : j = m2 + 1 + 1) (q : DecoF X.E (D.R.N j) (Pr.vT v) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))), HEq (pT c') q →
        HEq (pT c').deco.1.N q.deco.1.N ∧ ∀ c, HEq (fun x => σ (XiTop Ch sel mu cst (m2 + 1) (pt (m2 + 1) le_rfl c) (yb c) (pT c') x))
          (fun x => σ (XiTopG Ch sel mu cst (m2 + 1) j (D.R.N j) (pt (m2 + 1) le_rfl c) (yb c) q x)) := by
      intro j hj q hq
      subst hj
      obtain rfl := eq_of_heq hq
      exact ⟨HEq.rfl, fun _ => HEq.rfl⟩
    obtain ⟨g1, g2⟩ := gen D.R.m (by omega) p' hp
    refine ⟨?_, fun c => ?_⟩
    · rw [hTN c']
      refine g1.trans (heq_of_eq ?_)
      rw [hrow.1]
      rfl
    · have e : r.Xi (m2 + 1) c c' = fun x => σ (XiTop Ch sel mu cst (m2 + 1) (pt (m2 + 1) le_rfl c) (yb c) (pT c') x) := funext (hTX c c')
      rw [e]
      refine (g2 c).trans (heq_of_eq ?_)
      rw [xiTopTilQ_holds Ch sel mu cst hX hPr hc hm v hpi _ _ d p' hrow.1 hrow.2 (hyb c)]
  refine ⟨hSS, hlev, pt, ix, yb, fun c' => if h : ∃ d, OverRow sel mu v d (pT c') then some h.choose else none,
    hN, hyb, hE, hC, fun c' d hd => ?_, fun c c' d hd => ?_, hpin, fun c' => ?_⟩
  · dsimp only at hd
    split_ifs at hd with h
    obtain rfl := Option.some_inj.1 hd
    exact (key c' _ h.choose_spec).1
  · dsimp only at hd
    split_ifs at hd with h
    obtain rfl := Option.some_inj.1 hd
    exact (key c' _ h.choose_spec).2 c
  · rw [hpin' c']
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨_, dif_pos ⟨d, hd⟩⟩
    · rintro ⟨d, hd⟩
      dsimp only at hd
      split_ifs at hd with h
      exact h

section Gen
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xiOver_eq_topG {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl
end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def kerRd (u : B.Word) (a : I.ι) : KerRead ((I.rec7 l Z).chTw u a) B.fields where
  SS := Sall (Pr := B.primes X) I.sel (I.tup a) u
  lev := levC (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u
  N i c := ((I.stp u a i).rep c).1.1.deco.1.N
  Xi i c c' x := B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') x)
  pin i c := i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1

theorem kerRd_top {m2 : ℕ} (hm : B.R.m = m2 + 2) (u : B.Word) (a : I.ι) :
    (I.kerRd l Z u a).IsChainTop I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) B.embLL u m2 := by
  have hm' : (I.rec7 l Z).R.m = m2 + 2 := hm
  refine ⟨rfl, rfl, fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => Idx.get c.1 (by omega),
    fun c => ((I.stp u a (m2 + 1)).rep c).1.2, fun c => ((I.stp u a (m2 + 1 + 1)).rep c).1.1, fun _ _ _ => rfl,
    fun c => PtAt.mem_ybSet _ (by omega), fun i hi c c' x => ?_, fun c c' x => ?_, ⟨fun _ => rfl, fun c c' x => ?_⟩, fun i hi c => show i + 1 ≤ B.R.m ∨ _ from Or.inl (by omega), fun c' => ?_⟩
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm (Idx.some_get _ (by omega)).symm]
    rfl
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u m2 c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm]
    rfl
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (m2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega : m2 + 1 + 1 = B.R.m), xiOver_eq_topG]
    rfl
  · exact or_iff_right (by show ¬ m2 + 1 + 1 + 1 ≤ B.R.m; omega)

theorem mem_stdL_iff {R : Ranks} (H : Host R) (n : ℕ) (x : Fin n → H.E) : x ∈ Th.stdL H n ↔ ∀ k, IsIntegral ℤ (x k) := by
  refine ⟨fun h k => ?_, fun h k _ => Submodule.mem_one.2 ⟨⟨x k, h k⟩, rfl⟩⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h k trivial)
  rw [← hr]
  exact NumberField.RingOfIntegers.isIntegral_coe r

theorem chiRec_lat (hok : I.Ok) {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : B.Word) (a : I.ι) (i : ℕ)
    (c : (I.stp u a i).Cl) :
    TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) =
      I.chi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) := by
  have h1 := (O u a).dt_lat i c
  have h2 := hidl.2.2.2.2 _ ((O u a).L0 i) ((O u a).lat i c)
  rw [← h1] at h2
  have e0 : ((O u a).L0 i).1 = Th.stdL B.host (B.R.N i) := by
    ext x
    rw [(O u a).lattice_integral_coordinates]
    exact (mem_stdL_iff B.host _ x).symm
  have e1 : ((O u a).lat i c).1 = ((I.stp u a i).rep c).1.1.deco.1.N := hO.lat u a i c
  rw [e0, e1] at h2
  have h3 : Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N = idl (QuotientGroup.mk ((O u a).dt i c)) := h2.symm
  rw [h3, TaylorLogMetric.chiRec_idl _ _ hidl.1, ← h3]
  have h4 : ((TaylorLogMetric.chiQ (I.rec7 l Z) (QuotientGroup.mk ((O u a).dt i c)) : ℂˣ) : ℂ) = ((tildeQ B.host I.SQ I.C.chiPsi (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ) := by
    rw [hO.dt u a i c]
    rfl
  rw [h4]
  exact GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1

theorem kerRd_Th (hok : I.Ok) {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : B.Word) (a : I.ι) (i : ℕ)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    (I.kerRd l Z u a).Th (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (TaylorLogMetric.chiRec (I.rec7 l Z) idl) I.J.cD) i c c' =
      I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') := by
  refine (congrArg (fun A => (I.kerRd l Z u a).Th (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) A i c c')
    (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).symm).trans ?_
  have he : (I.J.amb B (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N =
      I.A.e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N := by
    funext z
    show Th.chiFac B.host _ _ _ _ _ * _ = Th.chiFac B.host _ _ _ _ _ * _
    unfold Th.chiFac
    rw [I.chiRec_lat l Z hok hidl hO u a i c, I.chiRec_lat l Z hok hidl hO u a (i + 1) c']
  show thC _ _ _ _ _ _ _ _ _ _ ((I.J.amb B (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) = thC _ _ _ _ _ _ _ _ _ _ (I.A.e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N)
  rw [he]
  rfl

theorem kerEntTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.Adapted ∧ t.TopPinned := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex O E hQ hO hU hE hS
  obtain ⟨idl, hidl⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  obtain ⟨⟨kf, hkf⟩, hAd⟩ := hE
  have hm := hok.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hok.sel_ok u ⟨hok.T_mem u, hok.g_mem⟩).2.1
  let t : KerEntTied ex :=
    { cc := ⊤
      cc_rec := B.toPre.ccK_top.symm
      cc_ok := ⟨top_ne_bot, by simp⟩
      δ := I.J.δ
      δ_ok := hok.amb_ok.delta
      B := I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      χ := TaylorLogMetric.chiRec (I.rec7 l Z) idl
      χ_ok := TaylorLogMetric.isChi_chiRec _ _ hidl
      idl := idl
      idl_ok := hidl
      χ_rec := rfl
      cD := I.J.cD
      X := B.fields
      seam := seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      seam_ok := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      Pr := B.primes X
      pr_ok := l.pr
      g_rec := fun i => rfl
      Ch := I.Ch
      sel := I.sel
      S := I.S
      word := fun u => u
      T_rec := fun u => rfl
      tup := I.tup
      Q_rec := hQ
      cst := I.cst
      idx := I.idx
      m2 := B.R.m - 2
      glob := I.glob
      glob_σ := rfl
      glob_xi := rfl
      idx_ok := hok.idx_ok
      O := O
      rd := I.kerRd l Z
      rd_chain := fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hok.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a)
      O_dgen := hO.dgen
      O_S := hO.S
      O_lat := fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
      O_Th := fun u a i c c' => (hO.Th u a i c c').trans (I.kerRd_Th l Z hok hidl hO u a i c c').symm
      unf := fun u a i hi => (hU u a i hi).unfIs _
      ent := E
      ent_lam := fun u w h => (hS u w h).1
      kf := kf
      kf_un := hkf
      served := hS }
  exact ⟨t, ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl,
    heq_of_eq (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J _).symm, rfl, hO⟩, rfl, hAd, fun u a => I.kerRd_top l Z hm u a⟩

end GlobalTheory.Mem.Col2.TC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterEigenvector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem omega_level_finVec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ t, ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i t, R.ωP i t (k, 1) (R.vP i t) = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩)⁻¹ : ℂˣ) : ℂ) • R.vP i t := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t k hf hk
  have hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
      (Formalism.IndefR.Lev.flag1L (R.datVt i t)) := hk
  have hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k := ⟨hf, hl.1, Subgroup.mem_bot.1 hl.2⟩
  have hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
    ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
  refine (GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 k 1 hκ hκ').trans ?_
  rw [Units.val_inv_eq_inv_val]
  exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t)
    (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm

end GlobalTheory.OneMapRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationFormLatticeIffClassValuesWeylLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_formLattice_iff_classValues_weylLattice : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (Pl : Rows.Places K) (w : Pl.Pl) (p : ℕ) [Fact p.Prime] (iL : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖iL x‖ ≤ 1) → ∀ x : S.FormsK emb lam h, x ∈ locW Pl w (S.latOf emb lam h fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.locW_latOf_iff | exact GlobalTheory.Mem.Col2.GStep.locW_latOf_iff | (intros; apply GlobalTheory.Mem.Col2.GStep.locW_latOf_iff <;> assumption)
end

