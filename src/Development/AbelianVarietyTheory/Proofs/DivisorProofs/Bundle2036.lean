import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0437
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpan
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

set_option maxHeartbeats 1000000 in

theorem pins_merge_of_clauses (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {ι x₀}
    (hsrc : ∀ j, (src j).Pins κ v₀ ι x₀)
    (hlift : ThPinsR R i jL₃ (inC c₃) v₀ c0₃ ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id))
    (hio : IoLFRec c₃ (fun τ => embF c₃ (tauE D τ)) (lamV D i) (wtA κ) io₃ hw₃)
    (hh : ∀ j, ∃ J', RepsR R i (tup j) (h j) ((src j).bad ()) J' ((src j).Lh ()) ((src j).gam ()) ((src j).vol ()))
    (c0 : ℂ) (hc0 : ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) (cs : J → ℂ) (hu : ∀ j, (u j : ℂ) * cs j = c0)
    (hcs : ∀ j, CXiAt (Wc D i) (rank_Wc i) (inC (src j).c') ((src j).dδ ()) ((src j).U₂ ()) ((src j).dict₂ ()) ι x₀
      ((src j).xi ()) (cs j)) :
    (merge src c₃ h₃ hs jL₃ hV₃ c0₃ lev io₃ hw₃ u h v₀).Pins κ v₀ ι x₀ := by
  have hu0 : ∀ j, u j ≠ 0 := fun j h0 => by
    obtain ⟨m, hm, e⟩ := hc0
    rw [← hu j, h0] at e
    simp [hm.ne'] at e
  refine ⟨hlift, fun j => ⟨?_, ((hsrc j).tuple ()).B, ((hsrc j).tuple ()).xi, ((hsrc j).tuple ()).phi, ((hsrc j).tuple ()).half⟩,
    ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).1⟩, fun j => (hsrc j).bad (), fun j => (hsrc j).reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ (hs j)) (((hsrc j).ep ()).1 k), epIs_map (hs j) ((hsrc j).ep ()).2⟩, hio,
    fun j k q => phiHat_covBC (hs j) _ (u j) _ _ q ((hsrc j).w () k q),
    fun j => covPin_covBC (hs j) _ (hu0 j) ((hsrc j).cov ()), ?_, fun j => (hsrc j).model₂ ()⟩
  · obtain ⟨J', hr⟩ := hh j
    obtain ⟨_, _, _, hT, hc⟩ := hlift.c0
    exact ⟨h j, J', repsR_map _ hr,
      GlobalTheory.RationalValues.placeEx R i jL₃ (inC c₃) (tup j) (h j) c0₃ hMo.jV hT hc hL hW hF.pl_onto hF.muVal,
      thAdIs_thAdOf R i (tup j) (h j) c0₃ hMo.HV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨c0, hc0, fun j => ?_⟩
    rw [← hu j]
    exact GlobalTheory.OneMapAll.cXiAt_covBC D _ _ _ _ _ _ _ _ (hs j) _ _ _ (u j) _ _ _ _ _ _ ((hsrc j).cov ()).1.2.2.2.2.2.2.2.1 (hcs j)

end Merge

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

variable {T R κ v₀}

set_option maxHeartbeats 1600000 in

theorem exists_extension_of_clauses (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    {i : Fin D.R.m} {ι x₀}
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T.toCore R i T0 id) (hle : O.c'.F ≤ O'.c'.F)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) (hO' : O'.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) :
    ∃ (M : OMDat T.toCore R i (Option T0) (fun o => o.getD A.μ0)) (h₁ : O.c'.F ≤ M.c'.F), M.lev = O.lev ∧
      M.Pins (κ i) (v₀ i (sg0 D A)) ι x₀ ∧
      ∀ x, O.Plc () x → ∃ x', M.Plc none x' ∧ M.thAd none x' = O.thAd () x ∧
        ∀ f ∈ sec _ O.c' (wtA (κ i)) (Vc D i).rank, IsSum O () x f → IsSum M none x' (rulBC h₁ f) := by
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  obtain ⟨b, hb, hcb⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO'.cxi
  obtain ⟨c₃, h', haF, hbF⟩ := exists_coeff_roots O'.c' ha hb
  have hb0 : b ≠ 0 := fun h0 => by
    obtain ⟨m, hm, e⟩ := hb
    simp [h0, hm.ne'] at e
  have h₁ : O.c'.F ≤ c₃.F := hle.trans h'
  have h₃ : T.Q.c.F ≤ c₃.F := O.hle.trans h₁
  have hV₃ : T.V ((i : ℕ) + 1) (sOv T.toCore c₃ h₃) = Wc D i := by
    rw [sOv_eq, ← sOv_eq T.toCore O.c' O.hle]; exact O.hV
  obtain ⟨c0₃, hc0⟩ := exists_coef_ext (incF O.c' c₃ h₁) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV D i) O.c0'
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.IoExtend.exists_ioLFRec_over _ _ _ _ O.c' c₃ h₁ _ _ (tauE D) (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  have hlift : ThPinsR R i ((incF O.c' c₃ h₁).comp O.jL) (inC c₃) (v₀ i (sg0 D A)) c0₃ ι T.Q.l.M (Mfr T.Q.l) O.lev := by
    refine ⟨(RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field, hO.lift.std, hO.lift.v0, ?_,
      hO.lift.lev⟩
    obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    obtain ⟨v'', hv''⟩ := GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) v'
    exact ⟨v'', by rw [hv'', hv', MvPolynomial.map_map], (hc0 v' v'' hv'').trans e⟩
  obtain ⟨h₀, J₀, hr₀, -, hth₀, hpl₀⟩ := (hO.tuple ()).reps
  choose hh Jt hrt _ using fun t => (hO'.tuple t).reps
  let src : ∀ o : Option T0, OMDat T.toCore R i Unit (fun _ => o.getD A.μ0) := fun o =>
    match o with
    | none => O
    | some t => comap O' (fun _ => t)
  have hs : ∀ o, (src o).c'.F ≤ c₃.F := fun o =>
    match o with
    | none => h₁
    | some _ => h'
  let u : Option T0 → c₃.F := fun o =>
    match o with
    | none => 1
    | some _ => ⟨a, haF⟩ / ⟨b, hbF⟩
  let h : ∀ o, (src o).Cl' () → GA D (Vc D i) := fun o =>
    match o with
    | none => h₀
    | some t => hh t
  have hP := pins_merge_of_clauses src c₃ h₃ hs _ hV₃ c0₃ O.lev io₃ hw₃ u h (v₀ i (sg0 D A)) hL hW hF hMo
    (fun o => match o with
      | none => hO
      | some t => pins_comap (fun _ => t) hO') hlift hO.act.1 hio
    (fun o => match o with
      | none => ⟨J₀, hr₀⟩
      | some t => ⟨Jt t, hrt t⟩) a ha (fun o => o.elim a fun _ => b)
    (fun o => match o with
      | none => one_mul a
      | some _ => div_mul_cancel₀ a hb0)
    (fun o => match o with
      | none => hca ()
      | some t => hcb t)
  refine ⟨_, h₁, rfl, hP, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (hpl₀ x).1 hx
  choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) (x k)
  have hy' : Place R i A.μ0 h₀ c0₃ (jVx R i A.μ0 y) x' := fun k => (hy k).trans (hc0 _ _ (hx' k)).symm
  refine ⟨x', ⟨y, hy'⟩, (thAdIs_thAdOf R i A.μ0 h₀ c0₃ hMo.HV hr₀.2.2.1 hr₀.2.2.2.2.2.1 _ _ _ hy').trans
    (hth₀ _ _ hy).symm, fun f hf hfx => ?_⟩
  exact isThClsD_covBC_one h₁ (O.dδ ()) rfl _ _ _ _ _ _ O.io io₃ x x' (fun k => hover _ _ (hx' k))
    (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx

variable (T R κ v₀)

theorem oneMapRowR_of_clauses (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    (hpins : OMPins T R κ v₀ O i) (htie : PhaseTie T R κ v₀ O ph i)
    (hrow0 : OneMapRow0 T R κ v₀ O i) (hex : PinnedDataExist T R κ v₀ i) (hid : IdentityRow T R κ v₀ i)
    (hspan : ClassSumsSpan (O i) (κ i)) : OneMapRowR T R κ v₀ O ph i := by
  refine ⟨hrow0, fun hG => ?_⟩
  obtain ⟨O', hLL', hP'⟩ := hex hG
  have hP := hpins.2
  rw [show O'.s0 = T.σ₀ from sOv_eq _ _ _] at hP'
  rw [show (O i).s0 = T.σ₀ from sOv_eq _ _ _] at hP
  obtain ⟨M, h₁, hlev, hM, hext⟩ := exists_extension_of_clauses hL hW hF hMo (O i) O' (hpins.1.le.trans hLL') hP hP'
  have hLM : D.what₂.embLL.toRatAlgHom.fieldRange ≤ M.c'.F := hpins.1.ge.trans h₁
  rw [← show M.s0 = T.σ₀ from sOv_eq _ _ _] at hM
  obtain ⟨cc', ph', hrow⟩ := hid _ _ M hLM hM
  exact ⟨comap M some, hLM, pins_comap some hM, oneMapOf_comap some
    (oneMapOf_of_extends (O i) M none h₁ hlev hM hext hspan (T.cE ((i : ℕ) + 1)) (htie hrow0) hrow)⟩

end Row

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLeTopLevelClassSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem KO_le_symPr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {G : Grid k} (hs : 1 ≤ G.s) (J : G.Level) (g : G.VertexGroup) {j : ℕ} (hj : j < G.m)
    (hJ : J (G.m, j) = KO k _)
    (hc : ∀ x : GL (Fin (topRank G j)) k, toFrame hs hj (g (G.m, j)) * embX (G.m - 1 - j) x =
      embX (G.m - 1 - j) x * toFrame hs hj (g (G.m, j))) :
    KO k (Fin (topRank G j)) ≤ symPr (conjLevel hs J g hj) := by
  intro x hx
  refine ⟨1, one_mem _, ?_⟩
  rw [one_mul, conjLevel, Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap]
  refine ⟨(g (G.m, j))⁻¹ * (toFrame hs hj).symm (embX _ x) * g (G.m, j), ?_, ?_⟩
  · rw [hJ]
    have e : toFrame hs hj ((g (G.m, j))⁻¹ * (toFrame hs hj).symm (embX _ x) * g (G.m, j)) = embX _ x := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact OneCosetProof.mem_KO_of_frameGL _ (by
      have := GlobalTheory.TwistVertex.embX_mem_KO (c := G.m - 1 - j) hx
      rw [← e] at this
      exact this)
  · simp [mul_assoc]

end GlobalTheory.LevTopCong

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem diag_comm_embX {k : Type} [Field k] {n : ℕ} {c : ℕ} (d : Fin c → kˣ) (x : GL (Fin n) k) :
    GlobalTheory.SplitFlip.diagGL (Sum.elim (fun _ => (1 : kˣ)) d) * embX c x =
      embX c x * GlobalTheory.SplitFlip.diagGL (Sum.elim (fun _ => (1 : kˣ)) d) := by
  refine Units.ext ?_
  have e : (diagonal fun i => ((Sum.elim (fun _ => (1 : kˣ)) d i : kˣ) : k)) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (diagonal fun p => (d p : k)) := by
    ext (i | i) (j | j) <;> simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hx : (embX c x).val = fromBlocks x.val 0 0 1 := rfl
  rw [Units.val_mul, Units.val_mul, GlobalTheory.SplitFlip.diagGL_val, e, hx, fromBlocks_multiply, fromBlocks_multiply]
  simp

end GlobalTheory.LevTopCong

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem KO_le_pr_stair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ G.s) (J : G.Level)
    (hJ : ∀ j, 0 < j → j < G.m → J (G.m, j) = KO k _) (ϖ : kˣ) (e : ℕ) (β : Cosets hs J)
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) {j : ℕ} (hj0 : 0 < j) (hj : j < G.m) :
    KO k (Fin (topRank G j)) ≤ symPr (conjLevel hs J ((Reps.through hs J (stair G ϖ e)).elt β) hj) := by
  refine KO_le_symPr hs J _ hj (hJ j hj0 hj) fun x => ?_
  obtain rfl : β = fun i : Fin (G.m - 2) => DoubleCoset.mk _ _ (stair G ϖ e (i + 1)) := funext hβ
  by_cases h2 : j + 2 ≤ G.m
  · rw [through_elt _ h2, toFrame_stair]
    exact diag_comm_embX _ _
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e1 : (Reps.through hs J (stair G ϖ e)).elt (fun i : Fin (G.m - 2) => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) (G.m, i + 1) = 1 := by
      rw [Reps.elt, onColumn_apply]
      simp [show ¬ i < G.m - 2 by omega]
    rw [e1, map_one, one_mul, mul_one]

end GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil in

theorem GlobalTheory.LevTopCong.congLev_le_levTop : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ j : Fin D.R.m, congLev D.sp.cm (ch.G.V (.top j)).gram (ch.G.Λ (.top j)) ch.G.modul ≤ ch.S.levTop A.μ0 Φ β j j.2 := by
  obtain ⟨CF0, hB⟩ := GlobalTheory.RowVal.oneAt
  refine ⟨CF0, fun CF hCF ε => ?_⟩
  obtain ⟨x₀, hx⟩ := hB ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx0 Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc _ Φ β hβ j => ?_⟩
  have hone := hx D large₂ hε hx0 Γ Pl0 T A Ks R F s ch hch hsc A.μ0 Φ β hβ
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hQ : R.Q A.μ0 = ∅ := Formalism.IndefR.FWT.Q_base_empty R hL
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => exact le_rfl
  | succ j =>
    intro g hg
    have hfr := ch.S.βp_is (j + 1) hj.le
    have hSt : g ∈ St (ch.S.βp (j + 1)) :=
      (GlobalTheory.LevSplit.mem_St_iff _ _ hfr g).2 (GlobalTheory.CongMember.stab_of_mem_congLev hg)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => LevRowSucc.KO_of_St rfl _ _ hSt⟩
    have hw0 : w.1 ∈ ch.G.pl.W0 := by
      have h2 := w.2
      simp only [locPl, Finset.mem_union] at h2
      rcases h2 with h2 | h2
      · exact h2
      · have h4 : (w : Pl D.host.E) ∈ R.Q A.μ0 := h2
        rw [hQ] at h4
        exact absurd h4 (Finset.notMem_empty _)
    refine GlobalTheory.LevTopCong.KO_le_pr_stair one_le_sLen _
      (fun i hi0 hi => GlobalTheory.RowVal.givenLevel_inner _ _ _ _ (by change 1 ≤ D.R.m; omega) hi0) _ _ (β w) (hone w hw0)
      j.succ_pos hj ?_
    exact LevRowSucc.KO_of_St _ _ _ hSt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsActFockVectorsAnyDatum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.FockAnyDatum

theorem om_ioP_of_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (φ : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg Q ξR (R.vacP i) φ → ∀ u ∈ GinfC (Vc D i), ∀ x w, R.ωP i A.μ0 (u, 1) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x w)) = pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x ((R.cV i).ρ u w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξR Q φ hφ u hu x w
  have hθ : IsInfFam R.θ := hR.models.inf
  have hω := hR.thP.ωP
  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hφ
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  have hthv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i A.μ0) := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hR.thP.vP i A.μ0
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  have hvφ := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hφ hthφ
  have hvv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hR.thP.vP i A.μ0) hthv
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ =>
    GlobalTheory.JointHarm.onb_eq_one (hR.models.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => IsUnit.of_mul_eq_one_right _ (hBS τ)
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hR.models.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank := fun τ =>
    (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).rank.1.trans hrk.symm
  have hfr : ∀ τ, (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ))
  have e : (fun τ => (R.MW i (sg0 D A)).fr τ * compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) *
      ((R.MW i (sg0 D A)).fr τ)⁻¹) = 1 := by
    funext τ; rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one, hfr]; rfl
  have act := fun (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) hv =>
    GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) _ (R.MW i (sg0 D A)) (R.BV i) (hω i A.μ0) hθ
      (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _
      (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T0 R.toLevCh A.μ0 hR.lev i A.μ0 τ).chiV)
      (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T0 R.toLevCh A.μ0 hR.lev i A.μ0 τ).chiW) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
      (fun τ => (hx τ).2.2.1) f hf hv u hu 1 (one_mem _)
      (fun τ => by rw [congrFun e τ]; exact GlobalTheory.JointHarm.one_mem_K)
  have aφ := (act φ hthφ hvφ).2
  have av := (act _ hthv hvv).2
  rw [e] at aφ av
  have hcV : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) τ) :=
    fun τ => by
      have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (hBu τ)
      have h1 := Matrix.mul_nonsing_inv _ hu'
      have hG : gramAt D (Vc D i) τ = ((R.BV i τ)⁻¹)ᴴ * (R.BV i τ)⁻¹ := by
        calc gramAt D (Vc D i) τ
            = ((R.BV i τ)⁻¹)ᴴ * ((R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ) * (R.BV i τ)⁻¹ := by
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one,
                Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
          _ = _ := by rw [hBS τ, Matrix.mul_one]
      refine ⟨Matrix.one_mul _, by simp, ?_⟩
      rw [Matrix.mul_one, hG]
      exact Matrix.PosDef.conjTranspose_mul_self _
        (Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 (hBu τ)))
  have hne : R.vP i A.μ0 ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βW i))
      (hrk.trans_le (r_le_V i)) (hR.thP.vP i A.μ0)
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hω i A.μ0).std hθ
    (fun _ => 1) (R.BV i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ hcV
    (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ) (hR.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hR.models.order i τ))
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) hthv hvv hne
  have key := (hR.thP.ioP i A.μ0).1 u hu x w
  unfold RealDat.ptP at key
  rw [av] at key
  rw [aφ, hinj key]

end GlobalTheory.FockAnyDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section
open GroundTheory.Global

namespace GlobalTheory.SubstIntertw

variable (F : Type) [Field F] [NumberField F]

def stdChar : AddChar (AF F) ℂ where
  toFun a := (adelicChar F a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem stdChar_inl (z : InfiniteAdeleRing F) :
    Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (infiniteAdeleInl z : AF F)) : ℝ)) =
      (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [h2, GlobalTheory.AdelicSvN.Weyl.trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_stdChar : IsStd (stdChar F) := by
  refine ⟨continuous_subtype_val.comp continuous_adelicChar, fun x => ?_, fun a ha => ?_⟩
  · show (adelicChar F (algebraMap F (AF F) x) : ℂ) = 1
    rw [adelicChar_algebraMap]; rfl
  · have h0 : evI F ((0, 1) : AF F) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
      exact map_zero _
    have h2 : a.2 = 0 := by
      have := congrArg Prod.snd (ha ((0, 1) : AF F) h0)
      have e : (1 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0 := this
      simpa using e
    obtain ⟨z, rfl⟩ : ∃ z : InfiniteAdeleRing F, a = infiniteAdeleInl z := ⟨a.1, Prod.ext rfl h2⟩
    exact (stdChar_inl F z).symm

end GlobalTheory.SubstIntertw

namespace GlobalTheory.SubstIntertw

open GroundTheory.Global

open scoped Classical in

theorem eval_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) x) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  show pureA F f g x = _
  simp [pureA, mul_comm]

theorem main : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ], ∀ (T : Module.End ℂ ((κ → AF F) → ℂ)) (a b : (κ → AF F) ≃ₗ[AF F] (κ → AF F)),
    (∀ f ∈ (adeleClass F).adm κ, f ∘ₗ T ∈ (adeleClass F).adm κ) →
    (∀ x y, ∀ Φ ∈ schA F κ, T (schr ψ (x, y) Φ) = schr ψ (a x, b y) (T Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ schA F κ, ∀ x, T Φ x = c * Φ (a.symm x) := by
  intro F _ _ hF ψ hψ κ _ T a b hadm hT
  haveI := hF
  have hstd := isStd_stdChar F
  obtain ⟨α, hα, hαψ⟩ := GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F (stdChar F) ψ (GlobalTheory.StdCharFromIsStd.isCharAF hstd) hψ
  set l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∘ₗ T with hl_def
  have hl : l ∈ (adeleClass F).adm κ := hadm _ (eval_mem_adm F κ 0)
  have hinv : ∀ (y : κ → AF F), ∀ φ ∈ schA F κ, l (fun x => stdChar F (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    have e : (fun x => stdChar F (x ⬝ᵥ y) * φ x) = schr ψ (0, algebraMap F (AF F) α⁻¹ • y) φ := by
      funext x
      simp only [schr, zero_dotProduct, mul_zero, add_zero, hαψ, dotProduct_smul, smul_eq_mul, ← mul_assoc,
        ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
    rw [e]
    show T (schr ψ (0, _) φ) 0 = T φ 0
    rw [hT _ _ φ hφ]
    simp [schr]
  obtain ⟨c, hc⟩ := GlobalTheory.CharInvForm.main F (stdChar F) hstd κ l hl hinv
  refine ⟨c, fun Φ hΦ x => ?_⟩
  have htr : ∀ v : κ → AF F, schr ψ (v, 0) Φ = schr (stdChar F) (v, 0) Φ := by
    intro v; funext z; simp [schr]
  have hmem : schr ψ (a.symm x, 0) Φ ∈ schA F κ := by
    rw [htr]; exact GlobalTheory.HeisSchA.schr_mem_schA (stdChar F) hstd _ Φ hΦ
  have h1 := hc _ hmem
  have h2 : l (schr ψ (a.symm x, 0) Φ) = T Φ x := by
    show T (schr ψ (a.symm x, 0) Φ) 0 = T Φ x
    rw [hT _ _ Φ hΦ]
    simp [schr]
  rw [← h2, h1]
  congr 1
  simp [schr]

end GlobalTheory.SubstIntertw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesBoundCoprimeTorsionMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie IsDedekindDomain
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option autoImplicit false
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortSeries_bound_coprime_torsion_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → AllRat Xo (xOf y) (N ^ 2) → (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp b ^ m = 1) → ∀ s : c.F, (∀ A : GlobalTheory.PlaceInt.Adapt Λ N ℓ, 0 ≤ nval T.V e (io (s * ∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ))) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (s * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  first | exact @GlobalTheory.SupFull.bound_of_coprime_mul | exact GlobalTheory.SupFull.bound_of_coprime_mul | (intros; apply GlobalTheory.SupFull.bound_of_coprime_mul <;> assumption)
end
end

