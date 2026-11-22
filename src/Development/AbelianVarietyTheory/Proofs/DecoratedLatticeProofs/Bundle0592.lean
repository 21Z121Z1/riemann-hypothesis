import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0034
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0530
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0590
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0580
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0458
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0571
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0573
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0533
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0067
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0591
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0550
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyDatum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoExists

section Transport

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem shape_upd {v : VCom c} {o : GlobalTheory.SeeSaw.TDat c k ι} (h : ShapeOff v o) (b Ψ ΨT JG eG eGT dG) :
    ShapeOff { v with b := b, Ψ := Ψ, ΨT := ΨT, JG := JG, eG := eG, eGT := eGT, dG := dG } o :=
  ⟨⟨h.pre.nodup, h.pre.all, h.pre.inj, h.pre.tP, h.pre.char, h.pre.latT, h.pre.line, h.pre.tau, h.pre.lam, h.pre.normT, h.pre.topT⟩,
    fun x => ⟨(h.good x).bf, (h.good x).fb⟩, fun x hx => ⟨(h.split x hx).core, (h.split x hx).top⟩, h.glued, h.rep, h.ram⟩

theorem moves_one (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves S 1 L L P := fun y _ => by
  have e : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [e, Matrix.one_mulVec]

theorem exists_places (D : D7) (T : ℕ) (hT : T ≠ 0) : ∃ s : Finset (GlobalTheory.FinPl.Pl D), ∀ p, p ∈ s ↔ ((T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  have h0 : Ideal.span {((T : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hT
  refine ⟨(Ideal.finite_factors h0).toFinset, fun p => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

end Transport

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

theorem meas_upd {a : XGeo D} {y : YRat a} {m : YMeas y} {b} (h : GeoMeas (pk W) (mkGeo m b)) (b') : GeoMeas (pk W) (mkGeo m b') :=
  ⟨h.μf, h.μT, h.ρJ, h.ρB, h.κ, h.vol, h.volT⟩

theorem tie_upd {f : FamCh W u} {v : VCom f.c} (h : VTie f v) (JG eG eGT dG) :
    VTie f { v with JG := JG, eG := eG, eGT := eGT, dG := dG } :=
  ⟨h.b, h.bT, h.gP, h.tP, h.moves, h.movesT, h.Ψ, h.ΨT, h.nz⟩

theorem selfDual_top (h : PkHyp W) : IsSelfDualC D.sp.X' (pk W).ΛX := by
  obtain ⟨c, hc⟩ := h.bot.hyp.2.2.2.1.lev.βX
  exact GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc

def xOf (A : GeoAll W u) : XGeo D := ⟨A.g.x, A.g.vac, A.g.Lz, A.g.oT, A.o.ζ₀, A.g.bT, A.g.LT⟩

set_option maxHeartbeats 2000000 in

theorem core (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (hPk : PkHyp W)
    (hTy : GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg) (hT0 : ((D.mem u).A.T : ℕ) ≠ 0)
    (hGT : ∀ PP ∈ (pk W).Pg, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (hQG : ∀ PP, QAll W PP → PP ∉ (pk W).Pg)
    (jj : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)) (hjj : TopReadAt W u jj 1)
    (a : XGeo D) (c₀ : ℕ → ℂ) (hx : ∀ j, j ≤ D.R.m → (a.x j).Is) (hbT : a.bT = 1) (hLT : a.LT = (pk W).ΛX)
    (hline : IsLineVec a.Lz a.ζ₀) (hn : star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E))
    (horth : ∀ n (h : n = D.R.m) (x : GlobalTheory.FinPl.Pl D), (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ x.asIdeal →
      ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x)
    (hloc : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → ∃ s : LocX a (pk W).βX PP,
      (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT)
    (R : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
      (p : ι → GlobalTheory.FinPl.SplitPt D k), (∀ j i, GlobalTheory.FinPl.Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)) →
        (∀ j, ι → GlobalTheory.LatPair.Pair k (Fin (D.sp.X j).rank)) → Prop)
    (hpre : ∀ (y : YRat a) (m : YMeas y) (b) (v : VCom (commOf (pk W) u (mkGeo m b))), v.NT = (pk W).ΛX →
      (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → v.τ = y.τ → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) →
      ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
        (o : GlobalTheory.SeeSaw.TDat (commOf (pk W) u (mkGeo m b)) k ι), PreT v o ∧ o.ζ₀ = a.ζ₀ ∧ R k ι o.p o.β o.Q) :
    ∃ A : GeoAll W u, A.Is ∧ A.c₀ = c₀ ∧ xOf A = a ∧ Framed A.d.B ∧ R A.k A.ι A.o.p A.o.β A.o.Q := by
  obtain ⟨y, Bt, h0, hτ, hlev, had, hfr, -, hz⟩ := GlobalTheory.T.line_vector_bessel_existence W u hPk a hline hn
  obtain ⟨m, hm₀, hlast⟩ := GlobalTheory.T.exists_geometric_measure_volume W u hPk a y (fun _ => 1) hx
  have hc₀ := GlobalTheory.Fam.commOf_is hD hH W u hPk _ hm₀ hx
  obtain ⟨tP, htP⟩ := exists_places D _ hT0
  obtain ⟨gP, hgP⟩ : ∃ s : Finset (GlobalTheory.FinPl.Pl D), ∀ p, p ∈ s ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F) :=
    ⟨(pk W).Pg.image fun PP => PP.under (𝓞 D.host.F), fun p => by simp only [Finset.mem_image, eq_comm]⟩
  have hdisj : Disjoint gP tP := Finset.disjoint_left.2 fun p h1 h2 => by
    obtain ⟨PP, hP, rfl⟩ := (hgP p).1 h1
    refine hGT PP hP ?_
    have h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.mem u).A.T : ℕ) ∈ PP.asIdeal := (htP _).1 h2
    rwa [map_natCast] at h3
  have hsd : IsSelfDualC D.sp.X' a.LT := hLT ▸ selfDual_top hPk
  let v₀ : VCom (commOf (pk W) u (mkGeo m fun _ => 1)) :=
    { gP := gP, tP := tP, N := fun _ => ⊥, NT := a.LT, b := fun _ => 1, bT := a.bT, Ψ := 0, ΨT := fun _ _ => 0, τ := y.τ, JG := fun _ => ⊥,
      eG := 0, eGT := fun _ _ => 0, dG := 0, cG := 0, RamAd := fun _ => ∅, Sad := fun _ => id, dT := 0,
      op := fun _ => ⟨0, Fin.elim0, Fin.elim0⟩ }
  obtain ⟨k, _, _, _, _, ι, o, hP, hζ, hR⟩ := hpre y m _ v₀ hLT htP rfl hτ
  choose l hlX hlT using hloc
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_symmetric_data_at_type_places W u hPk hTy a fun PP => l PP.1 (Or.inl PP.2)
  obtain ⟨bas, hb1, hb2⟩ : ∃ bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k,
      (∀ PP h, PP ∉ (pk W).Pg → bas PP h = fun _ _ _ => 1) ∧
      ∀ PP : (pk W).Pg, bas PP.1 (Or.inl PP.2) = fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc :=
    ⟨fun PP h => if hp : PP ∈ (pk W).Pg then fun j c hc => ((S ⟨PP, hp⟩).T (Fin D.R.t)).bas j c hc else fun _ _ _ => 1,
      fun PP h hp => dif_neg hp, fun PP => dif_pos PP.2⟩
  obtain ⟨N, b, dT, M, β₀, hsh, hb, hN, hY⟩ := GlobalTheory.T.local_component_vector_relation W u hPk a y m _ k ι v₀ o l bas hc₀ hτ hn rfl rfl hζ hsd hgP htP hP
    (fun n h x hx => horth n h x fun h' => hx ((htP x).2 h')) fun PP h hp j c hc => by rw [hb1 PP h hp]
  have hm := meas_upd hm₀ b
  have hc := GlobalTheory.Fam.commOf_is hD hH W u hPk _ hm hx
  have hbT' : a.bT ∈ GfC D.sp.X' := hbT ▸ Subgroup.one_mem _
  let v₁ : VCom (commOf (pk W) u (mkGeo m b)) :=
    { gP := gP, tP := tP, N := N, NT := a.LT, b := b, bT := a.bT, Ψ := 0, ΨT := fun _ _ => 0, τ := y.τ, JG := fun _ => ⊥,
      eG := 0, eGT := fun _ _ => 0, dG := 0, cG := 0, RamAd := o.Ram, Sad := fun _ => id, dT := dT,
      op := fun _ => ⟨0, Fin.elim0, Fin.elim0⟩ }
  obtain ⟨Ψ, ΨT, hΨ, hΨT, htie⟩ := GlobalTheory.T.local_component_places_characterized W u hPk a y m b v₁ hc rfl rfl hgP hTy (fun j => (hb j).1) hbT' hsd
    (fun P => by rw [hbT, hLT]; exact moves_one _ _ _) hN rfl rfl htP
  have hYG : ∀ PP : (pk W).Pg, LocY (l PP.1 (Or.inl PP.2)) y N (pk W).βY b fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc :=
    fun PP => hb2 PP ▸ (hY PP.1 (Or.inl PP.2)).some
  obtain ⟨JG, eG, eGT, dG, n, G, pl, hG, hat, hrd, hstd⟩ := GlobalTheory.LevPin.exists_levelData W u hPk a y m b { v₁ with Ψ := Ψ, ΨT := ΨT } hc rfl rfl hgP
    hTy _ S hS hYG fun PP => ⟨hlX _ _, hlT _ _⟩
  let v : VCom (commOf (pk W) u (mkGeo m b)) := { v₁ with Ψ := Ψ, ΨT := ΨT, JG := JG, eG := eG, eGT := eGT, dG := dG }
  choose Q hQ using fun PP (h : QAll W PP) => GlobalTheory.T.local_component_at_split_place W u hPk a y m b v hc rfl rfl PP h (l PP (Or.inr h))
    (hb1 PP (Or.inr h) (hQG PP h) ▸ (hY PP (Or.inr h)).some) (hlX _ _) (hlT _ _)
  have hv : v.Is :=
    ⟨hdisj, fun j hj => (hN j hj).1, hsd, fun j => (hb j).1, hbT', hΨ, hΨT, GlobalTheory.FixLev.fixLev_compact_open D _ v n G hG, hat,
      fun j => ⟨(hb j).2, fun i => i.elim0⟩, fun j φ hφ => ⟨hφ.1, hφ⟩⟩
  refine ⟨⟨mkGeo m b, jj, k, ι, v, { o with M := M, β₀ := β₀ }, n, G, pl, Q, ⟨Bt, b 0, 1, 1, 1⟩, c₀⟩,
    ⟨hm, hlast, hx, hv, shape_upd hsh b Ψ ΨT JG eG eGT dG, hG,
      fun row col => ⟨tie_upd (htie jj row col) JG eG eGT dG, hrd jj row col⟩, ?_, ?_, ?_, ?_, ⟨fun _ => hlev, rfl, had, hz⟩⟩,
    rfl, ?_, hfr, hR⟩
  · show TopReadAt W u jj a.bT
    rw [hbT]; exact hjj
  · show star o.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ o.ζ₀ = _ ∧ ∀ j h, y.τ j h *ᵥ o.ζ₀ = _
    rw [hζ]; exact ⟨hn, fun j h => (hτ j h).2⟩
  · intro i
    refine ⟨(hstd i).1, (hstd i).2.1, (hstd i).2.2.trans ?_⟩
    rw [← hζ]
  · intro PP h
    refine ⟨(hQ PP h).1, (hQ PP h).2.1, (hQ PP h).2.2.trans ?_⟩
    rw [← hζ]
  · show (⟨a.x, a.vac, a.Lz, a.oT, o.ζ₀, a.bT, a.LT⟩ : XGeo D) = a
    rw [hζ]

end Gen

set_option maxHeartbeats 2000000 in

theorem exists_geoAll : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ u : B.Word, ∃ a : GeoAll W u, a.Is ∧ a.True ∧ (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) ∧ GlobalTheory.MiTop.Framed a.d.B := by
  intro hD hH hS B X I l Z L hT Gi Gl Kc Yd cX ex W hW u
  obtain ⟨a, c₀, hx, hpin, hbT, hiA, hLT, hline, hn, hemb, hz, horth, hloc⟩ := GlobalTheory.T.all_true_family_geometry hS W hW u
  obtain ⟨jj, hjj⟩ := hW.tq.top1 u
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨A, hA, rfl, rfl, hfr, hR⟩ := core (W := W) (u := u) hD hH hW.pk hW.lev.1 (hPr.T_prime u).ne_zero
    (fun PP hP => Formalism.L2.Col.T_notMem_vGs hPr u ⟨PP, (hW.lev.2.1 PP).1 hP⟩)
    (fun PP ⟨t, ht⟩ hP => TC.Q_notMem_of_ok hW.tr.ok _ PP ((hW.tq.Q t PP).1 ht) ((hW.lev.2.1 PP).1 hP))
    jj hjj a c₀ hx hbT hLT hline hn (fun n h x _ => horth n h x) hloc
    (fun k _ _ _ _ ι p β Q => GlobalTheory.AdForm.StdT I l Z u p β Q fun j => (a.x j).L)
    fun y m b v h1 h2 h3 h4 => GlobalTheory.T.all_true_family_geometry_column W hW u (mkGeo m b) c₀ v a.ζ₀ hpin h1 h2 hline hz hemb
      (fun x _ => let ⟨LZ, _, ho⟩ := horth _ rfl x; ⟨LZ, hLT ▸ ho⟩) (by rw [h3]; exact h4)
  exact ⟨A, hA, ⟨hpin, hR, hemb, hz⟩, hiA, hfr⟩

end GlobalTheory.GeoExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfWeilDatumDescentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedThetaUnfolding_of_weilDatumDescent : ∀ D : D7, Descent D → IT D := by
  first | exact @GlobalTheory.Unf.iteratedUnfolding_of_descent | exact GlobalTheory.Unf.iteratedUnfolding_of_descent | (intros; apply GlobalTheory.Unf.iteratedUnfolding_of_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelPartLawsOfColumnPins
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KerLaws

theorem clsKL_is : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Is := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  refine ⟨?forms, ?real, ?lev, ?core, ?kval⟩
  case lev =>
    intro j hj α γ κ κ'
    exact GlobalTheory.T.chartLevelPair_action_finiteDatum_law I hOk hPins l Z u a Ch₀ k.Ch A ι _ _ _ _ _ _ _ _ _ _ _ hX hP j hj α γ κ κ'
  case core =>
    intro j hj α γ a₁ a₂ P'
    have hs := hS j hj
    have h1 := GlobalTheory.T.thetaKernelIdentity_at_every_tuple I hOk hPins l Z u a Ch₀ k.Ch A ι _ _ _ _ _ _ _ _ _ _ _ hX hP j hj (s j) hs.2 α γ a₁ a₂ P'
    have hx1 := hX.xs j (Nat.le_of_succ_le hj)
    have hx2 := hX.xs (j + 1) hj
    simp only [Tup.ker, KerDat.pt, realOf, clsKL, tupOf, commOf, hx1.1, hx1.2.1, hx2.1, hx2.2.1, if_neg hs.1]
    exact h1
  case forms =>
    refine ⟨fun j hj β => ?_, fun j hj β => ?_, fun j hj φ hφ β c => ?_, fun j hj φ hφ β y γ hγ c k₁ hk κ y' htr => ?_⟩
    · exact (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj (ι j β)).1
    · exact (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hOk hPins l Z u a Ch₀ A hP.is j hj (ι j β)).2.1
    · have hR := ((hP.ram j hj φ).1 hφ).1.1
      exact (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hP.is R.θ hX.inf j hj φ hR).1 c.1
    · have hR := ((hP.ram j hj φ).1 hφ).1.1
      have hx1 := hX.xs j hj
      have h2 := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hPins l Z u a Ch₀ A hP.is R.θ hX.inf j hj φ hR).2 (ι j β) y γ hγ c k₁ hk κ
        ⟨y'.1, y'.2⟩ (fun τ => by
          show y'.1 τ = _
          rw [htr τ]
          simp only [RealD.r, inN, inB, infM, realOf, commOf, hx1.2.1, inv_one, one_mul, mul_one]
          rfl)
      exact (congrFun (hP.rdq j hj β φ y) _).trans h2
  case real => exact GlobalTheory.T.livechart_kernelVectors_realPoints_detPowers I hOk hPins l Z u R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP
  case kval => exact GlobalTheory.T.liveCharts_kernel_eq_classSum_jets I hOk hPins l Z u R g c₀ s J hX hS hx P t r a k tl Ch₀ A ι w hP

end GlobalTheory.KerLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenXiIsLocFac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.Fam.PenLoc

def penXi {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} (a : GeoAll W u) (n : Fin a.n)
    (z : Matrix (Fin ((I.rec7 l Z).sp.X ((a.G n).s + 1)).rank) (Fin ((I.rec7 l Z).sp.X (a.G n).s).rank) (I.rec7 l Z).host.E) : ℂ :=
  ((a.G n).S.T (Fin B.R.t)).Psi 1
    (((a.G n).FX ((a.G n).s + 1) le_rfl).γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β)
    ((a.G n).S.y0 (Fin B.R.t))

theorem penXi_isLocFac : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n),
    GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (pk W).ψ _ _ (a.pl n).1 ((a.G n).cg (a.G n).s) (penXi a n) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col n
  have hR := (ha.tie row col).2
  letI := (a.G n).fld; letI := (a.G n).val; letI := (a.G n).top; letI := (a.G n).loc; letI := (a.G n).mea; letI := (a.G n).bor
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hid := (hR.idem n).1
  have hpf := GlobalTheory.LocMod.SymChainAt.place_facts (a.G n).q hid
  have hL : ∀ j, j ≤ B.R.m → IsSelfDualC _ (a.g.x j).L ∧
      ((a.g.x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec _ _ :=
    fun j hj => ⟨(ha.x j hj).sd, Set.ext (hat.pinX.xs j hj).2.2⟩
  exact ⟨(a.G n).k, _, _, _, _, ofSplit (a.G n).q, _, _, _, _, _, _, _, _, _, hpf.2, hid,
    GlobalTheory.SeeSaw.StdMatch.int_iff_up_mem (a.G n).q (a.G n).unit _ _ (hL _ (by omega)).1 (hL _ (by omega)).1 (hL _ (by omega)).2
      (hL _ (by omega)).2 ((a.G n).latX _ _) ((a.G n).latX _ _),
    GlobalTheory.LastTwoSteps.psi_mem_SB _ (Chain.ofType_regular _ _ _ _ _) _, (a.G n).cg_pen, fun _ => rfl⟩

end GlobalTheory.Fam.PenLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairVector
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem GlobalTheory.MiTop.line_ideal_atT : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (hr : 1 ≤ D.R.rS) u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → ((((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∨ (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) → ∀ c ∈ GlobalTheory.FinPl.idAt D (· = v), (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((pk W).ΛY 0) (· = v) ↔ Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f'.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((pk W).ΛY 0) (· = v)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' a₀ a a₀' a' _ _ v hv hT c hc
  have key : ∀ u₁ (f₁ : FamCh W u₁) (B₁ : SBes W.S.X W.Q.instEq u₁ W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f₁ B₁ →
      ∀ u₂ : D.what₂.Word, (((D.mem u₂).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      (Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f₁.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) ∈ GlobalTheory.FinPl.latV (D.sp.Y 0) ((pk W).ΛY 0) (· = v) ↔ c ∈ GlobalTheory.FinPl.intAt D (· = v)) := by
    intro u₁ f₁ B₁ h₁ u₂ h₂
    by_cases h : (((D.mem u₁).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
    · exact GlobalTheory.T.placed_bessel_away_places W hW hr u₁ f₁ B₁ h₁ v hv h c hc
    · exact GlobalTheory.T.placed_bessel_away_places_alt W hW hr u₁ f₁ B₁ h₁ v hv h u₂ h₂ c hc
  rcases hT with h | h
  · rw [key u f B hP u h, key u' f' B' hP' u h]
  · rw [key u f B hP u' h, key u' f' B' hP' u' h]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumSplitPlaceCombinationMulLocalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDatum_splitPlace_combination_mul_local : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) (fun γ => Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) f₀ (comb ψ S T c f) := by
  first | exact @GlobalTheory.LocMod.ratDatum_comb_place | exact GlobalTheory.LocMod.ratDatum_comb_place | (intros; apply GlobalTheory.LocMod.ratDatum_comb_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawTransportRelations_of_familyLaws : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  first | exact @GlobalTheory.SeeSaw.mainX_of_lawsX | exact GlobalTheory.SeeSaw.mainX_of_lawsX | (intros; apply GlobalTheory.SeeSaw.mainX_of_lawsX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallVectorCoefficientVanishesOffPrincipalLevelStatement
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
theorem _root_.GlobalTheory.T.smallVector_coefficient_vanishes_off_principalLevel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef om ν 𝓕 f f g = 0 := by
  first | exact @GlobalTheory.Core.Rk.Exh.SmallSupp.wcoef_eq_zero_off_prin | exact GlobalTheory.Core.Rk.Exh.SmallSupp.wcoef_eq_zero_off_prin | (intros; apply GlobalTheory.Core.Rk.Exh.SmallSupp.wcoef_eq_zero_off_prin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepDatumEqMulHalvesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepDatum_eq_mul_halves : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ S.rank) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (eG eQ : AE D), IsIdemSum eG Pg → IsIdemSum eQ Q → eG * eQ = 0 → ∀ x : WO S T, (if IsHalf (eG + eQ) x ∧ IsIntM (frMapO S T βS βT x) then omegaG (datY S.rank r t j hr Pg Q P χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q (datY S.rank r t j hr Pg Q P χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) = (if IsHalf eG (eG • x) ∧ IsIntM (frMapO S T βS βT (eG • x)) then omegaG (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eG • x))) * omegaQ ∅ (datY S.rank r t j hr Pg ∅ P χ (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO S T βS βT (eG • x))) else 0) * (if IsHalf eQ (eQ • x) ∧ IsIntM (frMapO S T βS βT (eQ • x)) then omegaG (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B) χj (fun PP => redM PP (frMapO S T βS βT (eQ • x))) * omegaQ Q (datY S.rank r t j hr ∅ Q (LevelP.triv ∅ r ℂ) χ ξ Frm.B).r ξ 1 (fun PP => redM PP (frMapO S T βS βT (eQ • x))) else 0) * (if IsHalf (eG + eQ) x then 1 else 0) := by
  first | exact @GlobalTheory.DatumHalves.stepDatum_eq_mul | exact GlobalTheory.DatumHalves.stepDatum_eq_mul | (intros; apply GlobalTheory.DatumHalves.stepDatum_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCoefVanishesOffLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainCoef_vanishes_off_level : ∀ D : D7, CoefSupp D := by
  first | exact @GlobalTheory.ChainOnto.CoefSuppPf.coefSupp | exact GlobalTheory.ChainOnto.CoefSuppPf.coefSupp | (intros; apply GlobalTheory.ChainOnto.CoefSuppPf.coefSupp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem readsExists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (commOf (pk W) u a.g).Is → ∀ t, ∃ J : QJ a t, J.Reads := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT hc t
  obtain ⟨J, hJ⟩ := GlobalTheory.T.true_geometry_commutation_value W hW u a ha haT hc t
  obtain ⟨J', hJ'⟩ := GlobalTheory.T.exists_readsStd_of_readsLow_of_allTrue W hW u a ha haT hc t J hJ
  exact GlobalTheory.T.true_geometry_commutation_property W hW u a ha haT hc t J' hJ'

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyFinal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

theorem GlobalTheory.QColLaws.laws_resc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), (a.fam row col).RowOK → (a.fam row col).ColOK →
    ∀ t (F : GlobalTheory.QPl.QFam a.v ((a.fam row col).t t)) (w₀ : VTup ((a.fam row col).t t)) (s : ∀ j, (col t).Ch j → ℂ),
    (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) → F.Pins w₀ →
    (∀ p, p ∈ w₀.Q ↔ ∃ PP ∈ (pk W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F)) →
    QLaw a.v (GlobalTheory.QTw.resc w₀ s) ∧ QLast a.v (GlobalTheory.QTw.resc w₀ s) ∧ QFin a.v (GlobalTheory.QTw.resc w₀ s) := by
  intro hDS hHC B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _haT row col hr hc t F w₀ s hs hPin hQ
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have hsh := ha.shape
  have hIs := GlobalTheory.T.family_rows_columns_valid hDS hHC W u hW.pk (a.fam row col) hr
  have hweil := GlobalTheory.T.family_chars_weilOK_unramified W u hW.pk (a.fam row col) a.v hr hc (ha.tie row col).1
    (fun j h => ⟨hsh.pre.line.1, hsh.pre.tau j h⟩) t w₀ hQ
  exact GlobalTheory.T.seeSawTwistPlaceLaws_of_rootOfUnityRescaling _ (a.fam row col).c a.v ((a.fam row col).t t) (GlobalTheory.QTw.resc w₀ s) hIs.1 (hIs.2 hc t) ha.vis hweil.1
    ⟨w₀, s, hs, ⟨F, hPin⟩, rfl⟩
end

