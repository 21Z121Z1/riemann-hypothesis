import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0596
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0597
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterMatchesWitnessStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chrEq_mu0_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ j : Fin q.B.R.m, Formalism.IndefR.Links.ChrEq ((pk (packB b)).mu0 ((j : ℕ) + 1)) (q.w.I.C.mu0 j) := by
  first | exact @GlobalTheory.Fam.level_character_matches_witness | exact GlobalTheory.Fam.level_character_matches_witness | (intros; apply GlobalTheory.Fam.level_character_matches_witness <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.BaseLevel

open NumberField IsDedekindDomain GlobalTheory.Mem.Col2 Formalism.L2.Forms GlobalTheory.SeeSaw GlobalTheory.SeeSaw.TopLevel

theorem levFn_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r t s : ℕ} (h : r ≤ n)
    (β) {SG Q : Finset (Pl E)} (P : LevelP SG r ℂ) (cg cg' : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (e : ∀ c, c < s → ∀ PP ∈ SG, cg (c + 1) PP = cg' (c + 1) PP) (g) :
    levFn (F := F) β ⟨r, h, t, s, SG, Q, P, cg, xq⟩ g = levFn (F := F) β ⟨r, h, t, s, SG, Q, P, cg', xq⟩ g := by
  unfold levFn
  congr 2
  refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c hc => ?_
  exact congrArg (fun f : (kP PP)ˣ →* ℂˣ => f _) (e c (Finset.mem_range.1 hc) PP hPP)

theorem isRes_unique {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem isRes_chiC (h : I.Ok) (j : Fin B.R.m) (PP : Pl (I.rec7 l Z).host.E) (hw : PP ∈ (B.primes X).vGs) :
    IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (chiC I j PP)⁻¹ := by
  intro a k u hk hu
  have ht := (h.ch_tied.mu0 j).atg ⟨PP, hw⟩ k a u hk hu
  have e : ∀ (j : Fin B.R.m) (P : HeightOneSpectrum (𝓞 B.fields.E)) (hw : P ∈ (B.primes X).vGs),
      Formalism.L2.Col.chiP I.Ch P j = I.Ch.chi j ⟨P, hw⟩ := by
    intro j P hw
    unfold Formalism.L2.Col.chiP
    rw [dif_pos hw]
    simp [Formalism.L2.Col.chiAt, Formalism.L2.Col.extChi]
  refine Units.ext (Eq.trans ?_ ht.symm)
  have e2 := (chiC_apply I j PP u).trans (congrArg (fun f : _ →* B.LLˣ => B.embLL ((f u : B.LLˣ) : B.LL)) (e j PP hw))
  exact (Units.val_inv_eq_inv_val _).trans ((congrArg (·⁻¹) e2).trans
    ((map_inv₀ B.embLL _).symm.trans (congrArg B.embLL (Units.val_inv_eq_inv_val _).symm)))

set_option maxHeartbeats 2000000 in

theorem topLev_datY (ok : I.Ok) (pins : TC.Pins B X) (v : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) (hF : I.StdF l Z v F) (hr : (I.rec7 l Z).R.r ≤ (I.rec7 l Z).sp.X'.rank)
    (P' : LevelP (B.primes X).vGs B.R.r ℂ) (cg : ℕ → ∀ PP : Pl B.fields.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl B.fields.E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (I.Ps w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (I.Ps w).H),
      ((P'.chi g : ℂˣ) : ℂ) = ∏ w, B.embLL (((I.Ps w).lam ⟨g.1 w, hg w⟩ : B.fields.Kˣ) : B.fields.K))
    (hcg : ∀ (j : Fin B.R.m), ∀ PP ∈ (B.primes X).vGs, IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (cg ((j : ℕ) + 1) PP)⁻¹) :
    GlobalTheory.Core.Rk.Top.TopLev F.clsP
      (levS (I.rec7 l Z).sp.X' 1 (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr (B.primes X).vGs ∅ P' cg ξ Frm.B))
      (levChi (I.rec7 l Z).sp.X' 1 (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr (B.primes X).vGs ∅ P' cg ξ Frm.B)) := by
  have hK := hF.what₂
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I ok pins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  obtain ⟨c', -⟩ := F.clsP.y_bij.2 (Quotient.mk'' 1)
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hR := rd_all I hK c'
  have hLb : F.clsP.lev.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  have key := @lev_iff B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ F.clsP.lev hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs I.Ps (Formalism.L2.Col.chiAt I.Ch) B.embLL hR
    P' (fun i => chiC I (i - 1)) (fun PP => (ξ PP)⁻¹) hH hchi
    (fun i PP a => by
      have e : Formalism.L2.Col.chiP I.Ch PP.1 = Formalism.L2.Col.chiAt I.Ch PP := dif_pos PP.2
      show B.embLL ((Formalism.L2.Col.chiP I.Ch PP.1 i a : B.LLˣ) : B.LL) = _
      rw [e])
  have hc : ∀ c, c < B.R.m → ∀ PP ∈ (B.primes X).vGs, cg (c + 1) PP = chiC I (c + 1 - 1) PP := fun c hc PP hPP =>
    inv_injective (isRes_unique (D := I.rec7 l Z) (hcg ⟨c, hc⟩ PP hPP) (isRes_chiC I l Z ok ⟨c, hc⟩ PP hPP))
  refine ⟨fun h => ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).1.2 κ.2⟩⟩, fun h κ hκ => ?_⟩
  · obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' h)
    exact ⟨⟨y, (key _ y hy).1.1 hh.2⟩, hh.1, hy⟩
  · refine Eq.trans ?_ ((key _ κ.1 hκ.2).2 κ.2)
    exact congrArg Units.val (levFn_congr (F := B.fields.F) hr 1 P' cg (fun i => chiC I (i - 1)) (fun PP => (ξ PP)⁻¹) hc _)

set_option maxHeartbeats 2000000 in

theorem topLev_levPOf (ok : I.Ok) (pins : TC.Pins B X) (v : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) (hF : I.StdF l Z v F) (hr : (I.rec7 l Z).R.r ≤ (I.rec7 l Z).sp.X'.rank)
    (Pg Q : Finset (Pl (I.rec7 l Z).host.E)) (β : GL (Fin (I.rec7 l Z).sp.X'.rank) (EAf (I.rec7 l Z)))
    (hPg : Pg = (B.primes X).vGs) (hQ : Q = ∅) (hβ : β = 1) (eG : R3.Gc B X ≃* G0 Pg (I.rec7 l Z).R.r)
    (hG : ∀ (g : R3.Gc B X) (P : Pl (I.rec7 l Z).host.E) (h : P ∈ (B.primes X).vGs) (h' : P ∈ Pg), eG g ⟨P, h'⟩ = g ⟨P, h⟩)
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hcg : ∀ (j : Fin B.R.m), ∀ PP ∈ Pg, IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (cg ((j : ℕ) + 1) PP)⁻¹) :
    GlobalTheory.Core.Rk.Top.TopLev F.clsP
      (levS (I.rec7 l Z).sp.X' β (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr Pg Q
        (levPOf (D := I.rec7 l Z) eG B.embLL (R3.lev1 I) (R3.chr1 I)) cg ξ Frm.B))
      (levChi (I.rec7 l Z).sp.X' β (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr Pg Q
        (levPOf (D := I.rec7 l Z) eG B.embLL (R3.lev1 I) (R3.chr1 I)) cg ξ Frm.B)) := by
  subst hPg hQ hβ
  have he : ∀ g w, eG.symm g w = g w := fun g w =>
    (hG (eG.symm g) w.1 w.2 w.2).symm.trans (congrFun (eG.apply_symm_apply g) w)
  refine topLev_datY I l Z ok pins v F hF hr _ cg ξ (fun g => ?_) (fun g hg => ?_) hcg
  · exact ⟨fun h w => he g w ▸ h w (Set.mem_univ w), fun h w _ => (he g w).symm ▸ h w⟩
  · have e := Formalism.L2.Col.LevFam.chr_apply (X := B.fields) I.Ps ⟨eG.symm g.1, g.2⟩
    refine (congrArg (fun x : B.fields.Kˣ => B.embLL (x : B.fields.K)) e).trans ?_
    show B.embLL ((∏ w, _ : B.fields.Kˣ) : B.fields.K) = _
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact congrArg (fun x => B.embLL (((I.Ps w).lam x : B.fields.Kˣ) : B.fields.K)) (Subtype.ext (he g.1 w))

def PairDataBaseTupleLevelEqualsClassLevel {D : D7} {O : Obj D} (x : R3.TwIn O.ex) {u : D.what₂.Word} (K₀ : ClsPTied u) : Prop :=
  ∀ t : x.T, x.Y.tup t = D.what₂.mu0 →
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ x.R.βX (datXP x.R.toRealDat (x.R.toRealDat.levR x.F.lv2 true) t))
      (levChi _ x.R.βX (datXP x.R.toRealDat (x.R.toRealDat.levR x.F.lv2 true) t))

set_option maxHeartbeats 2000000 in

theorem topLev_of_btw {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) (x : R3.TwIn O.ex) (y : Bl.BTw b x)
    {u : D.what₂.Word} (K₀ : ClsPTied u) (h : PairDataBaseTupleLevelEqualsClassLevel x K₀) (t : (packB b).P.T) (ht : (packB b).P.I.tup t = D.what₂.mu0) :
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t))
      (levChi _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) := by
  have key : ∀ k : Bl.RPk b.R b.S, k = Bl.rpkX y.y → ∀ t : k.P.T, k.P.I.tup t = D.what₂.mu0 →
      letI := k.B.alg
      GlobalTheory.Core.Rk.Top.TopLev K₀
        (levS _ k.B.Q.Rl.toRealDat.βX (datXP k.B.Q.Rl.toRealDat (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) t))
        (levChi _ k.B.Q.Rl.toRealDat.βX (datXP k.B.Q.Rl.toRealDat (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) t)) := by
    intro k hk
    subst hk
    exact h
  exact key (Bl.rpkB b) y.eq t ht

set_option maxHeartbeats 2000000 in

theorem Top_of_args {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K)
    (a : R3.TwArgs q.O.ex q.x.what₂) (v : q.B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((q.w.D q.Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (q.w.D q.Z) v Ch chOf) (hF : TC.StdF q.w.I q.w.l q.Z v F) : PairDataBaseTupleLevelEqualsClassLevel (O := q.O) a.x F.clsP := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F' cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  intro t ht
  have hT' : Y.tup = q.x.what₂.r.Y.tup := eq_of_heq htup
  have z := q.x.what₂.r.z.lev
  have hix : R3.ixOf q.w.I _ t = q.w.I.mu0 :=
    (q.x.what₂.r.tup_ix t).symm.trans ((congrFun hT' t).symm.trans ht)
  have hQ : q.x.what₂.r.z.R.Q t = ∅ := (z.Q t).trans ((congrArg q.w.I.Q hix).trans q.w.I.twistPrimes_reference_tuple_eq_empty)
  have hc := z.is.chi
  rw [z.C] at hc
  exact topLev_levPOf q.w.I q.w.l q.Z q.w.ok q.w.pins v F hF r_le_X q.x.what₂.r.z.R.Pg (q.x.what₂.r.z.R.Q t) q.x.what₂.r.z.R.βX
    z.Pg hQ z.beta.2 q.x.what₂.r.z.R.eG q.x.what₂.r.z.idG q.x.what₂.r.z.R.chi (q.x.what₂.r.z.R.xiR t) hc

set_option maxHeartbeats 2000000 in

theorem levG_base_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (packB b).P.T), (packB b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((packB b).R.T.cols.forms u).clsP.toG 1 (levS _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) (levChi _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) := by
  intro hL p K q c b hw u t ht
  obtain ⟨-, -, -, ⟨hC⟩, -⟩ := colsStd_of_bWit q b hw
  have hx : hw.a.x = hw.x := eq_of_heq hw.ax
  exact (levG_one_iff _ _ _).2 (topLev_of_btw b hw.x hw.y _ (hx ▸ Top_of_args q hw.a u _ (hC u)) t ht)

end GlobalTheory.Fam.BaseLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMatchOfWitnessStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_match_of_witness : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → GlobalTheory.Core.Mi.IdE b.S.X ∧ ∀ u, Formalism.L2.SG.ColDict.LevelMatch b.S.X (b.S.tr u) b.S.Y.hK := by
  first | exact @GlobalTheory.Core.Mi.idE_levelMatch_of_bwit | exact GlobalTheory.Core.Mi.idE_levelMatch_of_bwit | (intros; apply GlobalTheory.Core.Mi.idE_levelMatch_of_bwit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelTrueOfWitnessStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_true_of_witness : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → LevTrue (packB b) := by
  first | exact @GlobalTheory.Fam.BundleLev.levTrue_packB | exact GlobalTheory.Fam.BundleLev.levTrue_packB | (intros; apply GlobalTheory.Fam.BundleLev.levTrue_packB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffTwistedClass
section
noncomputable section

namespace GlobalTheory.TopVal.TwSet

section Gen

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

theorem lev_set {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E}
    (hJ' : J' = 1) (hJ : J = 1) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (hL : S.Lb = Formalism.L2.Col.stdLat E n) {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n') (ht : 0 < t) (hn : n = r + s * t)
    {SG Q : Finset (Pl E)} (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ)
    (hR : ∀ (z : GL (Fin n) (AfE F E)) (hz : z ∈ St (1 : GL (Fin n) (AfE F E))), z ∈ UAd hc n →
      (z ∈ S.U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (parFam h t s P χ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ blockTri (blk2 r)))
    (P' : LevelP SG r ℂ) (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H)
    (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hgy : ∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) :
    g ∈ lev hc J' 1 ⟨r, h', t, s, SG, Q, P', cg, xq⟩ ↔ y ∈ S.U := by
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, Q, P', cg, xq⟩ ↔
      g ∈ lev hc 1 1 (parDat h t s P χ) ∧ ∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    constructor
    · rintro ⟨⟨a1, a2, a3, a4⟩, a5⟩
      exact ⟨⟨⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, fun w _ => (hH _).1 a5 w⟩, a4⟩
    · rintro ⟨⟨⟨a1, a2, a3, -⟩, a5⟩, a4⟩
      exact ⟨⟨a1, a2, a3, a4⟩, (hH _).2 fun w => a5 w (Set.mem_univ w)⟩
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ∧ (∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r)) ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, hq⟩
      exact (hR g h2 h1).2 ⟨fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w), fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2⟩
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      obtain ⟨a, b⟩ := (hR g h2 h1).1 hy
      refine ⟨⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩, fun PP hP => ?_⟩
      · have := a w
        rwa [← hred h2] at this
      · have := b ⟨PP, hP⟩
        rwa [← hred h2] at this
  rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1]

theorem set_univ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ)
    (h1 : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (h2 : ∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P')
    (hR : RdLevOn hc (RatAt Q) S.U S.chi Λ emb Q HQ lamQ)
    (z : GL (Fin n) (AfE F E)) (hz : z ∈ St (1 : GL (Fin n) (AfE F E))) (hu : z ∈ UAd hc n) :
    z ∈ S.U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P :=
  (GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary hc hJ { S with chi := 1, chi_triv := fun _ _ => rfl } (fun w => ⟨(Λ w).H, 1⟩) emb HQ (fun _ => 1) h1 h2
    (Filter.Eventually.of_forall fun _ _ _ => rfl)
    (fun x hx hs hv => ⟨(hR x hx hs hv).1, fun _ _ _ => by simp⟩) z (Set.mem_univ z) hz hu).1

open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem under_inj {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ P P' : I.Q a, underPl B.host.F P.1 = underPl B.host.F P'.1 → P = P' := by
  classical
  intro P P' e
  rcases (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).1 (HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal e.symm)) with h | h
  · exact Subtype.ext h.symm
  · exact absurd (h ▸ Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P'.2))
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).1.split P.1 (Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P.2)))

set_option maxHeartbeats 2000000 in

theorem mem_levS_of_reads {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st} (hK : I.ReadsP a S.Lb S.U S.chi y lat st)
    (β : GL (Fin (I.rec7 l Z).sp.X'.rank) (Lev.EAf (I.rec7 l Z))) (hβ : β = 1)
    (Pg Q : Finset (Pl (I.rec7 l Z).host.E)) (hPg : Pg = (B.primes X).vGs) (hQ : Q = I.Q a)
    (P' : LevelP Pg B.R.r ℂ) (hH : ∀ g, g ∈ P'.H ↔ ∀ PP (h : PP ∈ (B.primes X).vGs) (h' : PP ∈ Pg), g ⟨PP, h'⟩ ∈ (I.Ps ⟨PP, h⟩).H)
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hr : B.R.r ≤ (I.rec7 l Z).sp.X'.rank) (g : Formalism.L2.Theta.GA (I.rec7 l Z) (I.rec7 l Z).sp.X') :
    g ∈ levS _ β (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr Pg Q P' cg ξ Lev.Frm.B) ↔
      ∃ κ : S.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  subst hβ hPg hQ
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hLb : S.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  let c : (I.stX a).Cl := ⟨(), Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩
  have hR0 := GlobalTheory.T.twistedTuple_reading_level_character I hOk hPins l Z a S hK c
    (fun PP => (Units.map B.embLL.toMonoidHom).comp
      (Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP)) (fun _ _ _ => rfl)
  have hR := set_univ (Q := I.Q a) B.sp.cm gP S (rowTyG I.Ch I.Ps) B.embLL _ _ (GlobalTheory.Mem.Col2.ChEx.q_conj I hOk a)
    (under_inj I hOk a) hR0
  have key := @lev_set B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ S hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs (I.Q a) I.Ps (Formalism.L2.Col.chiAt I.Ch) hR
    P' cg (fun PP => (ξ PP)⁻¹) (fun x => (hH x).trans ⟨fun h w => h w.1 w.2 w.2, fun h PP h1 _ => h ⟨PP, h1⟩⟩)
  refine ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).2 κ.2⟩⟩
  obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' g)
  exact ⟨⟨y, (key _ y hy).1 hh.2⟩, hh.1, hy⟩

end Gen

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Args

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 1000000 in

theorem lev_twArgs {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (g : G0 a.x.R.Pg (w.st Z).toD7.R.r) :
    g ∈ (a.x.R.toRealDat.levR a.x.F.lv2 true).H ↔
      ∀ PP (h : PP ∈ (B.primes w.px).vGs) (h' : PP ∈ a.x.R.Pg), g ⟨PP, h'⟩ ∈ (TC.Ps w.I ⟨PP, h⟩).H := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have key : ∀ g : G0 t.r.z.R.Pg (w.st Z).toD7.R.r, t.r.z.R.eG.symm g ∈ lev1 w.I ↔
      ∀ PP (h : PP ∈ (B.primes w.px).vGs) (h' : PP ∈ t.r.z.R.Pg), g ⟨PP, h'⟩ ∈ (TC.Ps w.I ⟨PP, h⟩).H := by
    intro g
    have e := fun PP h h' => t.r.z.idG (t.r.z.R.eG.symm g) PP h h'
    simp only [MulEquiv.apply_symm_apply] at e
    refine ⟨fun hg PP h h' => ?_, fun hg PP _ => ?_⟩
    · rw [e PP h h']
      exact hg ⟨PP, h⟩ (Set.mem_univ _)
    · have h' : PP.1 ∈ t.r.z.R.Pg := by
        have := t.r.z.lev.Pg
        exact (congrArg (PP.1 ∈ ·) this).mpr PP.2
      have := hg PP.1 PP.2 h'
      rw [e PP.1 PP.2 h'] at this
      exact this
  kexactB key g

end Args

set_option maxHeartbeats 2000000 in

theorem data_of_bWit {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c) (hw : Bl.BWit q b) :
    (pk (packB b)).βX = 1 ∧ (∀ t, (pk (packB b)).Q t = q.w.I.Q ((packB b).P.I.tup t)) ∧
      ∀ g, g ∈ (lvP (packB b)).H ↔ ∀ PP (h : PP ∈ (q.B.primes q.w.px).vGs) (h' : PP ∈ (pk (packB b)).Pg),
        g ⟨PP, h'⟩ ∈ (GlobalTheory.Mem.Col2.TC.Ps q.w.I ⟨PP, h⟩).H := by
  have hu := GlobalTheory.MiS.Check.used_all (packB b)
  obtain ⟨x, a, ax, y, -, -, -, -, -, -, -, -, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  subst hx
  obtain ⟨-, -, hl, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have key : ∀ k : Bl.RPk b.R b.S, k = Bl.rpkX y.y → (∀ t, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) (k.P.I.tup t)) →
      (letI := k.B.alg
      k.B.Q.Rl.toRealDat.βX = 1 ∧ (∀ t, k.B.Q.Rl.toRealDat.Q t = q.w.I.Q (k.P.I.tup t)) ∧
      ∀ g, g ∈ (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true).H ↔
        ∀ PP (h : PP ∈ (q.B.primes q.w.px).vGs) (h' : PP ∈ k.B.Q.Rl.toRealDat.Pg),
        g ⟨PP, h'⟩ ∈ (GlobalTheory.Mem.Col2.TC.Ps q.w.I ⟨PP, h⟩).H) := by
    intro k hk
    subst hk
    intro hu
    letI := a.x.grp
    letI := a.x.fin
    letI := a.x.alg
    refine ⟨a.x.pins.keep.beta.2, fun t => ?_, fun g => ?_⟩
    · have h1 := eq_of_heq (hl _ (hu t)).1
      exact (congrArg a.x.R.Q (a.x.Y.tupT_tup t)).symm.trans h1
    · exact (lev_twArgs a g)
  exact key (Bl.rpkB b) y.eq hu

set_option maxHeartbeats 2000000 in

theorem levS_iff_cls : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (packB b).P.T) (h : (packB b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X'), g ∈ (levS _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) ↔ ∃ κ : ((packB b).R.T.tw.pt.cls u ((packB b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1 := by
  intro hL p K q c b hw u t h g
  obtain ⟨hOk, ⟨hPins⟩, -, -, l0, tw, he, ht, -, -, s⟩ := GlobalTheory.Fam.colsStd_of_bWit q b hw
  obtain ⟨hβ, hQ, hH⟩ := data_of_bWit q b hw
  have hPg : (pk (packB b)).Pg = (q.B.primes q.w.px).vGs := Finset.ext (GlobalTheory.Fam.BundleLev.levTrue_packB q b hw).2.1
  have key : ∀ (Tw : TwForms (q.w.D q.Z)) (t' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes (packB b).R.T.n.tp (packB b).R.T.cols Tw),
      Tw = GlobalTheory.Mem.Col2.TC.tw q.w.I q.w.l l0 q.Z → HEq t' tw →
      (g ∈ (levS _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) ↔
        ∃ κ : (t'.pt.cls u ((packB b).P.I.tup t) h).lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1) := by
    rintro _ t' rfl rfl
    exact mem_levS_of_reads q.w.I hOk hPins q.w.l q.Z _ _ (s.what₂ u _ h) _ hβ _ _ hPg (hQ t) _ hH _ _ _ g
  exact key _ _ he ht

end GlobalTheory.TopVal.TwSet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairCharacterStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placed_bessel_pair_character : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((pk W).ΛY 0) v := by
  first | exact @GlobalTheory.MiTop.centralRatio_stab_atT | exact GlobalTheory.MiTop.centralRatio_stab_atT | (intros; apply GlobalTheory.MiTop.centralRatio_stab_atT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RankConditionAllMembersStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_condition_all_members : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  first | exact @GlobalTheory.Fam.MemberCount.member_rankMu | exact GlobalTheory.Fam.MemberCount.member_rankMu | (intros; apply GlobalTheory.Fam.MemberCount.member_rankMu <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitnessStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_data_of_witness : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → Formalism.IndefR.RealPins b.B.Q := by
  first | exact @GlobalTheory.Fam.realPins_of_bWit | exact GlobalTheory.Fam.realPins_of_bWit | (intros; apply GlobalTheory.Fam.realPins_of_bWit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarProductNonvanishingLevels
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem miStar2_of_families : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → LevHyp W → FamAllQ W → ServedQ W → PuNZ D → (cxW W).MIstar2 (W.Q.F.eV (cxW W).zs) W.Q.sEE := by
  intro hDS hCR hHC D L hT Gi Gl Kc Yd cX ex W hB hLv hFam hSv hPu
  exact GlobalTheory.T.joint_star_product_nonvanishing hDS hCR W hB (descent_eV_mem_level W hB hLv) (GlobalTheory.T.joint_of_family_and_service hCR hHC W hFam hSv) hPu

end GlobalTheory.MiTop

end
end

