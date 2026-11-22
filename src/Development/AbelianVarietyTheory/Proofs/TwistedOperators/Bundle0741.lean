import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0105
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0726
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0735
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0734
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0541
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0732
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0730
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0736
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0738
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSecRdUNeZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DictLevel

section NonZero

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal GlobalTheory.AdTh.GenConst
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem exists_sec_rdU_ne_zero (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (hr1 : 1 ≤ r) (k : U.Comp) (n : ℕ) (hn : Even n) (x : (U.X k).dom) (hux : IsUnitFr (U.X k) x.1) :
    ∃ f ∈ sec Xo c 0 n, Formalism.L2.PjFree.rdU U f k x.1 ≠ 0 := by
  have hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  let _ : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨-, hL, hmk, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := ThRead.cmHost_idempotent_trace_eq_one H
  have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun _ => antitone_const, hn⟩
  obtain ⟨Dc, he, -⟩ := exists_dic E H Dw l c σ r W.g n (U.X k) 0 W.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2 hL hD
  have hs := Dc.sympl
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n hs hn _ hw hw' _ hL 1 _
    (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  obtain ⟨A, hA, ϑ, hϑ, hmean⟩ := uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx hs
    (he ▸ Dc.per_eq) (he ▸ Dc.ty_eq) x hux
  have hT := isTheta1_of_reads_generator E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 _ _ A hs x.2 hL ϑ hϑ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r (U.X k) W.g Dc.bas Dc.idx n hs hn _ hw hw' _ hL v hv x.1 x.2 ϑ hT
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨Y, hY⟩ := (DualMark.dual_marking E H Dw l r (U.X k) _ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  obtain ⟨q, hq⟩ := exists_root_ne_zero hs hL x.2 hmk hY hT (ne_zero_of_meanOne hmean)
  obtain ⟨_, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond E H Dw l Xo c
  have hLaw : Laws := GlobalTheory.allSixLaws.1
  have hP := one_mem_harmA (Dw := Dw) c n
  obtain ⟨f, hf⟩ := (existsUnique_thRule Xo c nab (GlobalTheory.thValTot_of_chartIndep hLaw hC E H Dw l Xo c nab hnab)
    (fun b => levRep (q b)) hP).exists
  refine ⟨f, GlobalTheory.thetaRule_mem_sec hLaw hC E H Dw l Xo c nab hnab 0 n f ⟨_, _, hP, hf⟩, ?_⟩
  have hval := thVal_eq_thP hC E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 _ _ A hs x.2 hL Dw.p n Dc.hr
    Dc.eL hU.1 hn (he ▸ Dc.dir_eq) nab hnab ϑ v _ hϑ hv hκ (W.mark k) hmk hA (fun b => levRep (q b)) (Y q)
    (fun b => by
      obtain ⟨⟨a', ha', hq, hy⟩, hj⟩ := hY q b
      exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1
        (hq.trans (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q b))).symm), hy⟩, hj⟩) 0 1 hP _
    (ThRead.thValAt_evR hC Xo c nab hnab _ hP hf ℂ (unC U k x))
  have h2 := (fock_laws E r _ _ Dc.bas Dc.idx n hs hn x.1 x.2 1 ϑ).2.2.2.2 (fun _ => ϑ) _ v hv.1 hκ (Y q) 0
  have h3 : κ * thA (U.X k) Dc.bas Dc.idx (heisG (U.X k) Dc.bas (Y q) v) x.1 0 ≠ 0 := by
    refine h2 ▸ Finset.prod_ne_zero_iff.2 fun b _ => ?_
    rw [fock, Pi.zero_apply, zero_add, zero_add]
    exact mul_ne_zero (Complex.exp_ne_zero _) (hq b)
  rw [map_one, map_one, thP, polyDeriv_one] at hval
  exact fun h0 => h3 (hval.symm.trans ((dif_pos x.2).symm.trans h0))

end NonZero

section Scalar

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.GeoLevel GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix
open GlobalTheory.Dict (castFr IsUnitFr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Scalar

section Record

open NumberField IsDedekindDomain CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem finHom_mulVec_mul (V : HSp D) (κ κ' : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (κ * κ')).1 *ᵥ z = (finHom V κ).1 *ᵥ ((finHom V κ').1 *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem finHom_mulVec_one (V : HSp D) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V 1).1 *ᵥ z = z := by
  rw [map_one, Units.val_one, Matrix.one_mulVec]

def stabGrp (V : HSp D) : Subgroup (GA D V) where
  carrier := {κ | StabLat V κ}
  one_mem' := stabLat_one V
  mul_mem' := by
    rintro κ κ' ⟨a, h⟩ ⟨a', h'⟩
    refine ⟨mul_mem a a', ?_⟩
    unfold gLat at h h' ⊢
    rw [show (finHom V (κ * κ')).1.mulVec = (finHom V κ).1.mulVec ∘ (finHom V κ').1.mulVec from
      funext (finHom_mulVec_mul V κ κ'), Set.image_comp, h', h]
  inv_mem' := by
    rintro κ ⟨a, h⟩
    refine ⟨inv_mem a, ?_⟩
    unfold gLat at h ⊢
    conv_lhs => rw [← h]
    rw [← Set.image_comp, show (finHom V κ⁻¹).1.mulVec ∘ (finHom V κ).1.mulVec = id from funext fun z => by
      rw [Function.comp_apply, ← finHom_mulVec_mul, inv_mul_cancel, finHom_mulVec_one, id], Set.image_id]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
  {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}

end Record

end GlobalTheory.DictLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenStageFunctionRowArrowEqHalfExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.CosetRow

open Classical in

theorem givenFn_right_eq_extFn {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (B : Frames G) (t : T) (Φ : G.Datum) {e e₀ : AE D} (he : IsIdemSum e (locPl G t))
    (he₀ : IsIdemSum e₀ G.pl.W0)
    (hAA : ∀ w ∈ L.Q t, w ∉ G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) (i : Fin D.R.m) :
    GlobalTheory.FlipStart.givenFn B t Φ e (.right i 0) = GlobalTheory.CosetRow.extFn e₀ (e - e₀)
      (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _)
        (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i)) := by
  have hsub : G.pl.W0 ⊆ locPl G t := Finset.subset_union_left
  obtain ⟨he₁, h01⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he₀ hsub
  have hee : e₀ + (e - e₀) = e := add_sub_cancel e₀ e
  have h0 := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  obtain ⟨-, c0, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₀
  obtain ⟨-, c1, -⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he₁
  have hAA' : ∀ w ∈ locPl G t \ G.pl.W0, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := fun w hw => by
    rw [Finset.mem_sdiff] at hw
    exact hAA w ((Finset.mem_union.1 hw.1).resolve_left hw.2) hw.2

  have hmap : ∀ (a : AE D) (w : Pl D.host.E), cpt (D := D) w (toEAf D a) = 1 →
      ∀ x : WO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)),
      (a • x).map (cpt (D := D) w ∘ toEAf D) = x.map (cpt (D := D) w ∘ toEAf D) := fun a w ha x => by
    ext p q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Function.comp_apply, RingHom.map_mul, ha, one_mul]
  funext x
  unfold GlobalTheory.FlipStart.givenFn GlobalTheory.CosetRow.extFn
  rw [hee]
  by_cases hx : IsHalf e x
  swap
  · rw [if_neg hx, if_neg hx]
  rw [if_pos hx, if_pos hx]

  have hfac : ∀ w, givenDatum t w B Φ (edgeOf (.right i 0)) (locArg B t w (.right i 0) x) =
      if B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩
        (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i) then 1 else 0 := fun w => by
    have hh : (i : ℕ) < D.R.m ∧ 0 ≤ D.R.m := ⟨i.2, Nat.zero_le _⟩
    have hla : locArg B t w (.right i 0) x = B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
        ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) := by
      exact dif_pos hh
    rw [hla]
    simp only [edgeOf, givenDatum, dif_pos i.2, Set.indicator_apply, Pi.one_apply, Fin.eta]
  rw [Finset.prod_congr rfl fun w _ => hfac w, ← Finset.prod_sdiff hsub, Finset.prod_boole, Finset.prod_boole]
  have hx0 : IsHalf e₀ (e₀ • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h0]
  have hx1 : IsHalf (e - e₀) ((e - e₀) • x) := fun p q => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, h1]
  have k0 : cosInd e₀ (Φ i) (e₀ • x) = if ∀ w ∈ G.pl.W0, B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
      ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i)
      then 1 else 0 := by
    unfold cosInd
    rw [Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [GlobalTheory.FunObj.Comparison₂.mem_cosSet_iff_cosetSet B t hL he₀ i.2 (Φ i) hx0]
    exact forall₂_congr fun w hw => by rw [hmap e₀ w (c0 w hw)]
  have k1 : halfInd (e - e₀) (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _)
        (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) ((e - e₀) • x) = if ∀ w ∈ locPl G t \ G.pl.W0,
      B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0))
      ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (x.map (cpt (D := D) w ∘ toEAf D)) ∈ cosetSet t w B i.2 (Φ i)
      then 1 else 0 := by
    unfold halfInd
    refine if_congr ?_ rfl rfl
    rw [and_iff_left hx1, GlobalTheory.T.mem_completedGridArrowLattice_iff_integral_frameMatrix hL B t he₁ hAA' i _ hx1]
    refine forall₂_congr fun w hw => ?_
    rw [hmap _ w (c1 w hw), GlobalTheory.FunObj.Comparison₂.cosetSet_of_notMem B t w hL (Finset.mem_sdiff.1 hw).2 i.2 (Φ i)]
    rfl
  rw [k0, k1, mul_comm]

end GlobalTheory.CosetRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFourth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaArrowType

open GlobalTheory.Grid in

theorem sigOK_vert {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridPre R) (hG : G.Is) :
    ∀ i j, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).V.SigOK
  | 0, 0, _, _ => D.sp.Y_sig 0
  | 0, j + 1, _, _ => by
    show (row0 R (j + 1)).V.SigOK
    by_cases h : j + 1 < D.R.m
    · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]; exact D.sp.Y_sig _
    · rw [← nodeX_eq_chainVertexAtRowZero_of_ge R h]; exact D.sp.X'_sig
  | i + 1, j, hi, hj => (hG.spaces.vert i j hi hj).sigOK

theorem goodPar_of_node {D : D7} (N : GlobalTheory.Grid.Node D) (hV : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  obtain ⟨hp, hq⟩ := GlobalTheory.TypeAtCompare.card_eq_of_congr (N.M.fr_unit τ) (N.M.fr_gram τ) (hV (tauE D τ))
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), hp, hq⟩

theorem isTypeAt_lift_th : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) → ∀ τ, IsTypeAt R.θ (G.V i j).V τ ((G.V i j).S τ) (fun h => ∫ g in (G.meas t i (j + 1)).fd, thetaKO (G.th t i j).ω h g Φ * φ g ∂(G.meas t i (j + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ hint τ
  have hV := sigOK_vert G hG i j hi hj.le
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series R.θ (G.V i j).V τ ((G.V i j).S τ) _ hP.discreteSeriesUpqExists
    (GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hP.discreteSeriesHermitianUnique) hP.harishChandraModules
    hP.casselmanWallach hR.inf hV (goodPar_of_node (G.V i j) hV τ)
    (GlobalTheory.T.horizontal_theta_level_second hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint)
    (GlobalTheory.T.horizontal_theta_level_fifth hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hint τ)

end GlobalTheory.ThetaArrowType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdealMembershipOffModulus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.DepthIdeal

open GlobalTheory.SeeSaw (FI idV dI)
open GlobalTheory.FinPlLoc (idem)
open Formalism.IndefR.Fin

variable {D : D7}

theorem phiE_one (v : GlobalTheory.FinPl.Pl D) : phiE (D := D) v 1 = idem D (· = v) := by
  classical
  have h : sglV v (1 : v.adicCompletion D.host.F) = GlobalTheory.FinPlLoc.ePl D (· = v) := by
    apply af_ext; intro u
    rw [GlobalTheory.FinPlLoc.evalV_ePl]
    by_cases hu : u = v
    · subst hu; rw [sglV_same, if_pos rfl]
    · rw [sglV_ne v _ hu, if_neg hu]
  unfold idem
  rw [← h]
  rfl

variable {T : Type} {L : LevCh D T}

theorem belowPl_w (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) : belowPl (P.w v) = v := by
  conv_rhs => rw [← P.under_w hv]
  rfl

theorem exists_idem (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) {e : AE D} (he : IsIdemSum e P.W0) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f (P.w v) ∧ (1 - e) * idem D (· = v) = cA D f := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hmem : ∀ PP, PP ∈ P.W0 ↔ ∃ u ∈ P.S0, P.w u = PP := fun PP => by
    unfold Places.W0
    convert Finset.mem_image
  have hw : P.w v ∈ P.W0 := (hmem _).2 ⟨v, hv, rfl⟩
  have heps : ∀ u ∈ P.S0, es (P.w u) + cA D (es (P.w u)) = phiE u 1 := fun u hu => by
    have := below_of_idemAt (hes _ ((hmem _).2 ⟨u, hu, rfl⟩))
    rwa [belowPl_w P hu] at this
  have hfix : ∀ u ∈ P.S0, es (P.w u) * phiE u 1 = es (P.w u) := fun u hu => by
    have h := hes _ ((hmem _).2 ⟨u, hu, rfl⟩)
    rw [← heps u hu, mul_add, h.1.1, h.1.2.1, add_zero]
  refine ⟨es (P.w v), hes _ hw, ?_⟩
  have hsum : (∑ PP ∈ P.W0, es PP) * phiE v 1 = es (P.w v) := by
    rw [Finset.sum_mul, Finset.sum_eq_single (P.w v), hfix v hv]
    · intro PP hPP hne
      obtain ⟨u, hu, rfl⟩ := (hmem _).1 hPP
      have huv : u ≠ v := fun h => hne (h ▸ rfl)
      rw [← hfix u hu, mul_assoc, phiE_orth huv, mul_zero]
    · intro h; exact absurd hw h
  rw [← phiE_one, sub_mul, one_mul, hsum, ← heps v hv, add_sub_cancel_left]

theorem exists_modul_conj (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    ∃ x ∈ P.modul sc, ∃ y : 𝓞 D.host.E, y ∉ (P.w v).asIdeal ∧ (y : D.host.E) = star (x : D.host.E) := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ a ∈ (P.w u).asIdeal, ∃ b : 𝓞 D.host.E, b ∉ (P.w v).asIdeal ∧
      (b : D.host.E) = star (a : D.host.E) := by
    intro u hu
    by_cases huv : u = v
    · subst huv
      obtain ⟨f, hf⟩ := P.w_split u hu
      have hs := idemAt_split hf
      unfold Formalism.IndefR.Lev.IsConjPl at hs
      push Not at hs
      obtain ⟨a, ha, hb⟩ := hs
      exact ⟨a, ha, starO a, fun h => hb _ h rfl, rfl⟩
    · have hne : ¬ u.asIdeal ≤ v.asIdeal := fun hle =>
        huv (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle))
      obtain ⟨t, htu, htv⟩ := Set.not_subset.1 hne
      refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, ?_⟩
      · have : t ∈ (belowPl (P.w u)).asIdeal := by rw [belowPl_w P hu]; exact htu
        exact this
      · intro h
        apply htv
        have : t ∈ (belowPl (P.w v)).asIdeal := h
        rwa [belowPl_w P hv] at this
      · rw [algebraMap_O]
        exact (D.sp.cm.sig.commutes _).symm
  choose! a ha b hb hab using hu
  refine ⟨∏ u ∈ P.S0, a u ^ P.depth sc u, ?_, ∏ u ∈ P.S0, b u ^ P.depth sc u, ?_, ?_⟩
  · exact Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow (ha u hu) _
  · intro hmem
    obtain ⟨u, hu, hmem'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (P.w v).isPrime)).1 hmem
    exact hb u hu ((P.w v).isPrime.mem_of_pow_mem _ hmem')
  · change algebraMap (𝓞 D.host.E) D.host.E _ = star (algebraMap (𝓞 D.host.E) D.host.E _)
    rw [map_prod, map_prod, star_prod]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [map_pow, map_pow, star_pow]
    exact congrArg (· ^ P.depth sc u) (hab u hu)

theorem idV_le_dI (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v ≤ idV (dI D) v := by
  refine GlobalTheory.StairLine.idV_le_of_loc fun z hz => ⟨_, GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces P hv, ?_⟩
  have e : dI D = D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) := by
    unfold dI; ring
  have e2 : algebraMap D.host.F D.host.E ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) =
      ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) := by
    rw [← algebraMap_O, map_natCast]; rfl
  rw [e, e2]
  exact FractionalIdeal.mul_mem_mul (GlobalTheory.HostClear.absNorm_mem_AA D) hz

theorem compl_mem (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) {e : AE D} (he : IsIdemSum e P.W0)
    (𝔞 : FI D) {s : AE D} (hs : s ∈ idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) v) :
    (1 - e) * idem D (· = v) * s ∈ idV 𝔞 v := by
  obtain ⟨f, hf, hfe⟩ := exists_idem P hv he
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_modul_conj P sc hv
  have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  have hx0 : (x : D.host.E) ≠ 0 := by
    intro h
    apply hy0
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [map_zero]
    change (y : D.host.E) = 0
    rw [hxy, h, star_zero]
  have hm0 : ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 (P.modul_ne_bot sc)
  have h1 : idem D (· = v) * incA D x ∈ idV ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) v := by
    unfold idem
    rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, mul_one]
    refine GlobalTheory.SeeSaw.IdVMul.gen_mem (GlobalTheory.FinPlLoc.ePl_int _) (fun w hw => ?_)
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨x, hx, rfl⟩)
    rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]
  have h2 := GlobalTheory.SeeSaw.IdVMul.mul_mem_idV h1 hs
  rw [mul_left_comm, mul_inv_cancel₀ hm0, mul_one] at h2
  have hint : finPart D (cA D f * incA D (x : D.host.E)⁻¹) ∈ intAE D := by
    have h3 : finPart D (f * incA D (y : D.host.E)⁻¹) ∈ intAE D := not_not.1 (mt (hf.2 y hy0).2 hy)
    have h4 := cF_int h3
    rwa [← finPart_cA, cA_mul_incA, hxy, star_inv₀, star_star] at h4
  have h5 : cA D f * incA D (x : D.host.E)⁻¹ ∈ idV (1 : FI D) v := by
    refine (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ⟨?_, hint⟩
    rw [← hfe]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _))
  have h6 := GlobalTheory.SeeSaw.IdVMul.mul_mem_idV h5 h2
  rw [one_mul, ← hfe] at h6
  have e1 : incA D (x : D.host.E)⁻¹ * incA D x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have e2 := GlobalTheory.FinPlLoc.idem_mul_self (D := D) (· = v)
  have e3 : (1 - e) * idem D (· = v) * incA D (x : D.host.E)⁻¹ * (idem D (· = v) * incA D x * s) =
      (1 - e) * idem D (· = v) * s := by
    calc _ = (1 - e) * (idem D (· = v) * idem D (· = v)) * (incA D (x : D.host.E)⁻¹ * incA D x) * s := by ring
      _ = _ := by rw [e1, e2, mul_one]
  rwa [e3] at h6

theorem mem_dI_of_half : All fun {D} _ _ _ {G} _ _ => ∀ v ∈ G.pl.S0, ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ s ∈ idAt D (· = v), s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D * ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → e * s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v → s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
  intro D _ T L μ0 _ sc G W M _ v hv e he s hs h1 h2
  have hA := idV_le_dI G.pl hv h2
  have hB := compl_mem G.pl sc hv he (dI D) h1
  rw [mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ s).1 hs] at hB
  have := add_mem hA hB
  rwa [← add_mul, add_sub_cancel, one_mul] at this

end GlobalTheory.DepthIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedHomLattice_iff_integral_on_unit_half : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ z : WO S T, IsHalf e₁ z → (z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w))) := by
  first | exact @GlobalTheory.ColLatDict.mem_latO_iff_intM | exact GlobalTheory.ColLatDict.mem_latO_iff_intM | (intros; apply GlobalTheory.ColLatDict.mem_latO_iff_intM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeOfMemLatticeHomCosetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedHomLattice_of_mem_latticeHomCoset : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}, IsSelfDualC S ΛS → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → (∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1) → ∀ {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos ΛS ΛT 𝔪) {t : WO S T}, t ∈ cosSet e κ → t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet | exact GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet | (intros; apply GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFunctionTotalTensorInvariantLastArrowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productFunction_totalTensor_invariant_lastArrows : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.grid D.R.m D.R.m), finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D)
        (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D)))) j (w j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) i (v i)) =
    τ.sum fun d a => a * (∏ j, S.Z.vec (d.1 j) (w j)) * ∏ i, S.Z.vec (d.2 i) (v i) := by
  first | exact @GlobalTheory.LastVertexTensor.productFn_invariant | exact GlobalTheory.LastVertexTensor.productFn_invariant | (intros; apply GlobalTheory.LastVertexTensor.productFn_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaDifferByTwistValuesLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedVacua_differ_by_twist_values_largeDepth : Big fun ch => VacTw ch := by
  first | exact @GlobalTheory.RowVacTw.vacTw | exact GlobalTheory.RowVacTw.vacTw | (intros; apply GlobalTheory.RowVacTw.vacTw <;> assumption)
end

