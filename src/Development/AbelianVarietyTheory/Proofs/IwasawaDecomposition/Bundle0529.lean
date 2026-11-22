import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0514
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationRulesHold
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelActionsOnLiftRulesExtendedDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.ActExt

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.LevelActionPinned
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

private theorem congr_of_two_lifts {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : V.rank = L.r) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} (hM0 : M ≠ 0) {Mb Mh : Ideal (𝓞 D.host.E)}
    (hMb : Mb = ∏ PP ∈ L.Pg, PP.asIdeal) (hM : Mb * Mh = Ideal.span {(M : 𝓞 D.host.E)}) (hcop : Mb ⊔ Mh = ⊤)
    {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {u u' : La →ₗ[𝓞 D.host.E] La}
    (hu : ∃ κ, Lev.IsLevelLift V β L g0 κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (u a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w)
    (hu' : ∃ κ, Lev.IsLevelLift V β L g0 κ ∧ ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (u' a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = M • w) (a : La) :
    u' a - u a ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La) := by
  obtain ⟨κ, hκ, h1⟩ := hu
  obtain ⟨κ', hκ', h1'⟩ := hu'
  have hM₁ : (∏ PP ∈ L.Pg, PP.asIdeal) * Mh = Ideal.span {(M : 𝓞 D.host.E)} := by rw [← hMb, hM]
  have hMm : (M : 𝓞 D.host.E) ∈ Mb :=
    Ideal.mul_le_left (I := Mb) (J := Mh) (by rw [hM]; exact Ideal.mem_span_singleton_self _)
  have hst := mulVec_mem_of_St hβ (Formalism.L2.DIV.parLev_St hκ.2.1)
  have hd := Lev.lift_div_mem hκ hκ'
  obtain ⟨s, hs, v, hv, huv⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ Mb ⊔ Mh)
  have hva : v • a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La) := Submodule.smul_mem_smul hv Submodule.mem_top
  obtain ⟨w₁, hw₁, e₁⟩ := h1 _ hva
  obtain ⟨w₂, hw₂, e₂⟩ := h1' _ hva
  obtain ⟨w₃, hw₃, e₃⟩ := lift_one_congr (L := L) hβ hL hι hM₁ hd.2.1 (Subgroup.mem_bot.1 hd.2.2) _ hva
  have e₄ : (finHom V κ').val = (finHom V κ).val * (finHom V (κ⁻¹ * κ')).val := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have e₅ : fvec V ι (u' (v • a) - u (v • a)) = M • (w₂ - w₁ + (finHom V κ).val *ᵥ w₃) := by
    have e₁' : fvec V ι (u (v • a)) - (finHom V κ).val *ᵥ fvec V ι (v • a) = M • w₁ := e₁
    have e₂' : fvec V ι (u' (v • a)) - (finHom V κ').val *ᵥ fvec V ι (v • a) = M • w₂ := e₂
    rw [smul_add, smul_sub, ← Matrix.mulVec_smul, ← e₁', ← e₂', ← e₃, map_sub, e₄, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  obtain ⟨x, hx⟩ := exists_eq_nsmul hι hM0 _ _ (add_mem (sub_mem hw₂ hw₁) (hst _ hw₃)) e₅
  have e₆ : u' a - u a = s • (u' a - u a) + (M : 𝓞 D.host.E) • x := by
    rw [Nat.cast_smul_eq_nsmul, ← hx, map_smul, map_smul, ← smul_sub, ← add_smul, huv, one_smul]
  rw [e₆]
  exact add_mem (Submodule.smul_mem_smul hs Submodule.mem_top) (Submodule.smul_mem_smul hMm Submodule.mem_top)

private theorem latEmb_iota {D : D7} (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have key : ∀ (V : HSp D) (_ : T.V ((i : ℕ) + 1) T.toCore.σ₀ = V) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) := by
    rintro V rfl hr
    obtain ⟨_, -, -, -, -, -, -, hemb, -⟩ := hT.adPin _ (inR i) _ T.toCore.good_σ₀
    exact hemb
  exact key _ (hT.spaceW _ (inR i) _ T.toCore.good_σ₀) (rank_Wc i)

private theorem act_heq {D : D7} (i : Fin D.R.m)
    {β β' : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)} (eβ : β' = β)
    {Λ : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)} (hβ : IsSDFrame (Wc D i) (β i) Λ 1)
    {Pg Pg' : Finset (Formalism.L2.DIV.Pl D.host.E)} (eP : Pg' = Pg)
    {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {ι : ∀ j, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} {ι' : ∀ j, (Dw' j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)}
    (hι : HEq ι' ι)
    (hemb : LatEmb (Wc D i) (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)))
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal)
    {G : Type} [Group G] {eG : G ≃* G0 Pg D.R.r} {eG' : G ≃* G0 Pg' D.R.r} (heG : HEq eG' eG)
    {lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La}
    {lev' : G → (Dw' ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw' ((i : ℕ) + 1)).La}
    (hlev : ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β i)
        (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG g) κ ∧
      ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) (Dw ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
        finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)) (lev g a)) -
          (finHom (Wc D i) κ).1.mulVec
            (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι ((i : ℕ) + 1)) a)) = l.M • w)
    (hlev' : ∀ g, ∃ κ, Lev.IsLevelLift (Wc D i) (β' i)
        (datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg' ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B) (eG' g) κ ∧
      ∀ a ∈ Mfr l' • (⊤ : Submodule (𝓞 D.host.E) (Dw' ((i : ℕ) + 1)).La), ∃ w ∈ latGHat (Wc D i) 1,
        finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι' ((i : ℕ) + 1)) (lev' g a)) -
          (finHom (Wc D i) κ).1.mulVec
            (finVec (Wc D i) ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ ι' ((i : ℕ) + 1)) a)) = l'.M • w)
    (g : G) (r : Rul (Xo ((i : ℕ) + 1)) c) (r' : Rul (Xo' ((i : ℕ) + 1)) c') (hr : HEq r' r) :
    HEq (actLev (Xo := Xo' ((i : ℕ) + 1)) c' (fun g => (lev' g, LinearMap.id)) g r')
      (actLev (Xo := Xo ((i : ℕ) + 1)) c (fun g => (lev g, LinearMap.id)) g r) := by
  subst eβ eP hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hι
  obtain rfl := eq_of_heq heG
  obtain rfl := eq_of_heq hr
  have key : ∀ g a, lev' g a - lev g a ∈ l'.Mb • (⊤ : Submodule (𝓞 D.host.E) (Dw' ((i : ℕ) + 1)).La) := fun g a =>
    congr_of_two_lifts
      (L := datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg' ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B)
      hβ (rank_Wc i) hemb (by have := l'.three_le; omega) hMb l'.prod l'.coprime (hlev g) (hlev' g) a
  have e : (fun {S : Type} [CommRing S] [Algebra c'.F S] (g : G) (y y' : FrPt (Xo' ((i : ℕ) + 1)) c' S) =>
        levActR (Xo := Xo' ((i : ℕ) + 1)) (c := c') (fun g => (lev' g, LinearMap.id)) g y y') =
      fun {S : Type} [CommRing S] [Algebra c'.F S] (g : G) (y y' : FrPt (Xo' ((i : ℕ) + 1)) c' S) =>
        levActR (Xo := Xo' ((i : ℕ) + 1)) (c := c') (fun g => (lev g, LinearMap.id)) g y y' := by
    funext S _ _ g y y'
    exact propext (GlobalTheory.LevelActionOfLifts.levR_congr (key g) y y')
  unfold actLev
  rw [e]

private theorem geo_facts {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {ph : Fin D.R.m → ℂ}
    (B : GlobalTheory.RealGeo.GeoHalf T R ph) (i : Fin D.R.m) :
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (B.O i).lev ∧ T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧ LatEmb (Wc D i) (iotaW T i) :=
  ⟨(B.pins i).2.lift.lev, ((B.pins i).2.tuple ()).half.1, latEmb_iota T B.fw.laws i⟩

end GlobalTheory.Mem.R3.ActExt

set_option maxHeartbeats 2000000 in
theorem _root_.GlobalTheory.T.levelActions_on_liftRules_extendedData : StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g →
        ∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r →
          HEq (Formalism.L2.Pj.actLev z'.core.Q.c (z'.geo.O j').lev2 g' r') (Formalism.L2.Pj.actLev z.core.Q.c (z.geo.O j).lev2 g r) := by
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj g g' hg r r' hr => ?_
  obtain ⟨h1, h3, h4⟩ := GlobalTheory.Mem.R3.ActExt.geo_facts z.geo j
  obtain ⟨h2, -, -⟩ := GlobalTheory.Mem.R3.ActExt.geo_facts z'.geo j'
  have h5 := z.lev.is.βW j
  have hB := hE.1
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e
  cases w with | mk px => ?_
  cases w' with | mk px' => ?_
  dsimp only at hpx px px'
  cases hpx
  have eg : g' = g := eq_of_heq hg
  subst eg
  exact GlobalTheory.Mem.R3.ActExt.act_heq j' (eq_of_heq hx.βW) h5 (eq_of_heq hx.Pg) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.iota h4 h3 hx.eG h1 h2 g' r r' hr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeights
section
noncomputable section

namespace GlobalTheory.Mem.SRe.SxPass

section Mv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl Formalism.L2.SG.ColDict Formalism.L2.SG.HidaSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {F F' : ∀ u, Forms0 D u}

set_option maxHeartbeats 4000000 in

def trCar (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) : Transport X u (F' u) :=
  { t with
    hc_rep := fun c => by rw [(h u).2.2.2.1]; exact t.hc_rep c
    J_isom := fun c ξ η => by rw [(h u).2.2.2.2]; exact t.J_isom c ξ η }

set_option maxHeartbeats 4000000 in
theorem colDictL_car (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) (hK : X.LevelSubgroupCharacter) :
    colDictL X (trCar h t) hK = colDictL X t hK := by
  refine LinearMap.ext fun T => funext fun c => funext fun z => ?_
  exact congrArg (fun e => t.J (shP X u T.1 (t.hc c)) (e z)) (congrArg DFunLike.coe (h u).2.2.2.2)

theorem chi_of_heq {G : Type} [Group G] {U U' : Subgroup G} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} (e : U' = U) (h : HEq chi' chi)
    (x : G) (hx : x ∈ U') : chi' ⟨x, hx⟩ = chi ⟨x, e ▸ hx⟩ := by
  subst e
  rw [eq_of_heq h]

set_option maxHeartbeats 4000000 in
theorem lev_car (h : SameCar F F') {X : HidaSetting D} {u} {t : Transport X u (F u)} {hK : X.LevelSubgroupCharacter} (l : LevelMatch X t hK) :
    LevelMatch X (trCar h t) hK := by
  refine ⟨fun x => ?_, fun g y hr => ⟨?_, fun hk hy => ?_⟩⟩
  · rw [(h u).1]; exact l.1 x
  · rw [(h u).2.1]; exact (l.2 g y hr).1
  · rw [chi_of_heq (h u).2.1 (h u).2.2.1]; exact (l.2 g y hr).2 hk _

set_option maxHeartbeats 4000000 in

def packCar (h : SameCar F F') (P : SPack D F) : SPack D F' :=
  { P with
    tr := fun u => trCar h (P.tr u)
    into := fun u T => by rw [colDictL_car]; exact P.into u T
    bij := fun u => by unfold ColDictBij; rw [colDictL_car]; exact P.bij u
    lev := fun u => lev_car h (P.lev u)
    isom := fun u a b => by rw [colDictL_car]; exact P.isom u a b }

set_option maxHeartbeats 4000000 in

def restCar (h : SameCar F F') {P : SPack D F} (S : SRest P) : SRest (packCar h P) where
  hI := S.hI
  autTie := S.autTie
  colPin := fun u x => Subtype.ext ((LinearMap.congr_fun (colDictL_car h (P.tr u) P.Y.hK) _).trans (congrArg Subtype.val (S.colPin u x)))
  j := S.j
  rowPin := S.rowPin
  locTied := S.locTied

set_option maxHeartbeats 4000000 in

def satCar (h : SameCar F F') (p : RowPk D) (s : p.SAt F) : p.SAt F' :=
  { P := packCar h s.P, S := restCar h s.S, t := s.t, c := s.c, c_pos := s.c_pos, see := s.see, ev := s.ev, rowJ := s.rowJ }

end Mv

section Slot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 8000000 in

theorem sxMv : SxMv := by
  intro K B f T w Z Wt p0 r col N h p0' t col' e ⟨s⟩
  obtain ⟨F₁, hF⟩ := exists_sameF_ofDiv (D := Late.D Z) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :))) fun u => (col.C.forms u).to0
  obtain ⟨s', -⟩ := GlobalTheory.T.spectralComparison_transported_divisionLatticeChange B w.C Z (pkOf r).G' (pkOf r).Pl0 (pkOf r).T (pkOf r).A (pkOf r).Ks (pkOf r).R (pkOf r).F
    (fun u => (col.C.forms u).to0) (pkOf r).eE (cast (sx_eq r col) s) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (hF :)))
  have c := StdUnique.sameStd B f T w Z (New.ofDiv (Late.D Z) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :)))) col ((by with_unfolding_all exact (col' :))) ((by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (hF :)))
  have e' : pkOf t = (pkOf r).up Z Z.S N h := eq_of_heq e
  rw [sx_eq t col', e']
  exact ⟨satCar (D := Late.D (upL Z Z.S N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) ((pkOf r).up Z Z.S N h) ((by with_unfolding_all exact (s' :)))⟩

end Slot

end GlobalTheory.Mem.SRe.SxPass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupLatticeExtendedDataEqCoordinatewiseImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section
namespace GlobalTheory.Mem.R3.MKExt
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cusp_match {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f' : cusp (Xo' j') c' (U' j') a' n') :
    ∃ f : cusp (Xo j) c (U j) a n, HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f', HEq.rfl, Iff.rfl⟩

theorem cusp_match' {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : Host E} {Dw : ℕ → Datum H}
    {Dw' : ℕ → Datum H'} {l : Level H} {l' : Level H'} {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'}
    {c : Coeff l} {c' : Coeff l'} {r : ℕ} {U : ∀ j (σ : c.F →+* ℂ), Unf (Xo j) c σ r}
    {U' : ∀ j (σ : c'.F →+* ℂ), Unf (Xo' j) c' σ r} (hH : H' = H) (hDw : HEq Dw' Dw) (hl : HEq l' l)
    (hXo : HEq Xo' Xo) (hc : HEq c' c) (hU : HEq U' U) {j j' : ℕ} (hj : j' = j) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ}
    (ha : a' = a) (hn : n' = n) (f : cusp (Xo j) c (U j) a n) :
    ∃ f' : cusp (Xo' j') c' (U' j') a' n', HEq f' f ∧
      ((∀ la, ∀ v ∈ valSet (Xo' j') c' (algCls (Xo' j') c') la, 0 ≤ v (f' : Rul (Xo' j') c')) ↔
        (∀ la, ∀ v ∈ valSet (Xo j) c (algCls (Xo j) c) la, 0 ≤ v (f : Rul (Xo j) c))) := by
  subst hH; cases hDw; cases hl; cases hXo; cases hc; cases hU; subst ha; subst hn; subst hj
  exact ⟨f, HEq.rfl, Iff.rfl⟩

theorem extendByZero_eq_of_heq_families {Tau : Type} (p : ℕ → ℕ) {j j' : ℕ} (hj : j' = j) {a : Tau → Fin (p j) → ℕ}
    {a' : Tau → Fin (p j') → ℕ} (h : HEq a' a) (t : Tau) : ext0 (a' t) = ext0 (a t) := by
  subst hj; cases h; rfl

section Comparison₂
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem nrm_le_one_iff (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m)
    (f : T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) :
    (∀ la (y : (R.FW i).Pt la), (R.FW i).nrm la y (fw.e i f) ≤ 1) ↔
      ∀ la, ∀ v ∈ valSet (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (algCls (T.Q.Xo ((i : ℕ) + 1)) T.Q.c) la,
        0 ≤ v (f : T.R ((i : ℕ) + 1)) := by
  constructor
  · intro h la v hv
    have h1 := h la ((fw.pt i la).symm ⟨v, hv⟩)
    rw [fw.nrm_eq, Core.nrmM_le_one_iff, Equiv.apply_symm_apply] at h1
    exact h1
  · intro h la y
    rw [fw.nrm_eq, Core.nrmM_le_one_iff]
    exact h la _ (fw.pt i la y).2

end Comparison₂

end GlobalTheory.Mem.R3.MKExt

namespace GlobalTheory.Mem.R3.MKExt
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 4000000 in

theorem mk_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ((z'.R.FW j').MK : Set (Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)) = {x' | ∃ x ∈ (z.R.FW j).MK, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hN j j' hj φ hφ => ?_
  obtain ⟨hB, -⟩ := hE
  clear * - hB hN hj φ hφ
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have M1 := fun f' => cusp_match hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f'
  have M2 := fun f => cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 f
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  ext x'
  simp only [SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨f', he'⟩ : ∃ f', z'.geo.fw.e j' f' = ⟨x', h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f, hff, hP⟩ := M1 f'
    have hI' : ∀ la (y : (z'.R.FW j').Pt la), (z'.R.FW j').nrm la y (z'.geo.fw.e j' f') ≤ 1 := by
      rw [he']; exact h2
    have hI := hP.1 ((nrm_le_one_iff z'.geo.fw j' f').1 hI')
    have hx' : ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) = x' :=
      congrArg Subtype.val he'
    refine ⟨((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL),
      ⟨(z.geo.fw.e j f).2, (nrm_le_one_iff z.geo.fw j f).2 hI⟩, fun k k' hk => ?_⟩
    have h3 := hN.forms j j' hj f f' hff k k' hk
    apply hinj
    rw [hφ]
    exact (congrArg (fun v => (w'.st Z').toD7.what₂.embLL (v k')) hx').symm.trans h3
  · rintro ⟨x, ⟨h1, h2⟩, hrel⟩
    obtain ⟨f, he⟩ : ∃ f, z.geo.fw.e j f = ⟨x, h1⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨f', hff, hP⟩ := M2 f
    have hI : ∀ la (y : (z.R.FW j).Pt la), (z.R.FW j).nrm la y (z.geo.fw.e j f) ≤ 1 := by
      rw [he]; exact h2
    have hI' := hP.2 ((nrm_le_one_iff z.geo.fw j f).1 hI)
    have hx : ((z.geo.fw.e j f : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = x :=
      congrArg Subtype.val he
    have hx' : x' = ((z'.geo.fw.e j' f' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
      funext k'
      have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
      have h3 := hN.forms j j' hj f f' hff (Fin.cast hn k') k' hk
      have h4 := hrel (Fin.cast hn k') k' hk
      apply hinj
      rw [h4]
      exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
    subst hx'
    exact ⟨(z'.geo.fw.e j' f').2, (nrm_le_one_iff z'.geo.fw j' f').2 hI'⟩

end GlobalTheory.Mem.R3.MKExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationRulesHoldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationRules_hold : ∀ D : D7, WeilRules D := by
  first | exact @GlobalTheory.Mem.WeilRule.weilRules | exact GlobalTheory.Mem.WeilRule.weilRules | (intros; apply GlobalTheory.Mem.WeilRule.weilRules <;> assumption)
end

