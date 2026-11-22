import Formalism.SharpRestriction.InertJacobiLevels.ExtraNew
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0003
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
import Formalism.SharpRestriction.InertJacobiLevels.ExtraEnt
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.TieTTwValsOfMem

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.GaugeExists
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure Shape (D : D7) : Prop where
  mult : ∀ μ j, Subsingleton (D.what₂.Mult μ j)
  amb : ∀ μ, Subsingleton (D.what₂.Amb μ)
  mtL : ∀ μ j, Subsingleton (D.what₂.MtL μ j)
  mj : ∀ j, Subsingleton (D.what₂.Mj j)
  ee0 : Subsingleton D.what₂.EE0
  rr : Subsingleton D.div.RR.V
  nu : ∀ u, Subsingleton (D.div.Nu u).V
  lat : ∀ u j, Subsingleton ((D.fm u).lat j).V
  yTw : ∀ u μ i, IsEmpty ((D.chTw u μ).Y i)
  clsTw : ∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))
  mtV : ∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)
  fmN : ∀ i j b, Subsingleton (D.nexp.Fm i j b)
  ll0 : ∀ x : D.what₂.LL, x ∈ D.LL0
  Ij0 : ∀ μ j w, D.what₂.Ij μ j w = 0
  jw0 : ∀ μ j w, D.what₂.jw μ j w = 0
  drows : D.what₂.Drows = 0
  dgam : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamMink D
  loc : IsEmpty D.nd.Loc
  gatM : ∀ u w h, (D.gat u w h).M = ⊥
  gatComp : ∀ u w h, Nonempty ((D.gat u w h).comp ≃ (D.chTw u (D.what₂.muAt w)).cls 0)
  gatTr : ∀ u w h (c : (D.gat u w h).comp) (L L' : (D.gat u w h).P.Tup), (D.gat u w h).P.IsLatTup L →
    (D.gat u w h).P.IsLatTup L' → ∃ γ : ((D.gat u w h).lev c).Γ, L' = ((D.gat u w h).lev c).smul γ L

structure LevErr (D : D7) where
  lev : LevelData D
  errX : ErrX D
  piG_lev : PiGLevel D lev errX
  piT_lev : PiTLevel D lev errX
  seen : SeenDef D errX
  tauOf : TauOfDef D errX

def GaugeExists {R : Ranks} (H : Host R) (sp : @Spaces R H.F H.E _ _ _ _ H.cmStar _) : Prop :=
  letI := H.cmStar
  ∃ G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam H.F H.E sp.cm.sig, G.IsGauge

structure ExtraIn (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (X : DivX D) (cX : ExtraC) where
  shape : Shape D

  mjH : ∀ j, Subsingleton (X.MjH j).V
  kapR : X.kapR D.what₂.embLL = 1

  compS : ∀ u w h j, IsEmpty ((Gl.Lv u w h).compS j)
  vram : ∀ u w h, Gl.Vram u w h = ⊥
  latTied : G.LatTied hT Gi Gl

  ep_def : G.EpDef Gi cX.Ce
  ep_tie : EpTie Gi
  kapI_def : G.KapIDef Gi K
  fills_all : FillsAll hT Gl
  fdef : L.FDef

  kap_def : DV.KapDef D
  duStar_def : ∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u
  Dstar_def : D.what₂.Dstar = StandardLattice.DstarD D
  cover : NTw.TwCover D.ntw

  le : LevErr D
  served : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ServedEmb D u w h
  gauge : GaugeExists D.host D.sp

  large : cX.err.Large
  edef : L.EDef le.errX K cX.err

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D}
  {K : G.Consts} {X : DivX D} {cX : ExtraC}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def extraOf (I : ExtraIn D L hT Gi Gl K X cX) : Extra D L hT Gi Gl K X cX :=
  haveI := I.shape.mult
  haveI := I.shape.mtL
  haveI := I.shape.mj
  haveI := I.shape.ee0
  haveI := I.shape.nu
  haveI := I.shape.lat
  haveI := I.shape.yTw
  haveI := I.shape.mtV
  haveI := I.shape.fmN
  haveI := I.mjH
  haveI := I.shape.clsTw
  haveI := I.shape.loc
  { lev := I.le.lev
    th := thetaZero D
    th_io := thetaZero_io D
    cmp := latCmpZero D I.shape.gatM I.served
    lat := latDefsZero D I.shape.gatM I.served Gi Gl K I.vram
    tw := twFormsZero D
    ker := fun u w h =>
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      haveI := I.shape.clsTw u (D.what₂.muAt w)
      haveI := I.compS u w h
      kerZeroE D hT I.shape.gatM I.served (twFormsZero D) (plEmb D) u w h (Gl.Ch u w h) (I.latTied u w h).2.1 (I.latTied u w h).1
        (I.shape.gatComp u w h).some (I.shape.gatTr u w h) (exists_latTup _)
    ep_def := I.ep_def
    ep_tie := I.ep_tie
    kapI_def := I.kapI_def
    fills_all := I.fills_all
    nu_unserved := nuUnserved_zero Gi K
    idx := idxDefs_zero D X I.shape.Ij0 I.shape.jw0
    kap_def := I.kap_def
    lam_def := lamDef_zero D
    kapR_def := kapRBase_zero X I.shape.drows I.kapR
    errX := I.le.errX
    err := ⟨I.large, I.le.piG_lev, I.le.piT_lev, I.le.seen, I.le.tauOf, dGamDef_of D I.shape.dgam, I.edef⟩
    nch := nchZero D (nchEmbOf D I.shape.ll0 I.cover)
    nch_tie := nchTie_zero D I.shape.ll0 I.cover
    xd := thDataZero D
    p0 := trivialSide D
    rationalRoots_def := trivialSide_rrDef_of_subsingleton D
    amb := haveI : ∀ μ, Subsingleton ((RowSide.sharp D).Amb μ) := I.shape.amb; ambZero D _
    amb0 := ambZero D _
    fdef := I.fdef
    duStar_def := I.duStar_def
    Dstar_def := I.Dstar_def
    gauge := I.gauge.choose
    gauge_def := I.gauge.choose_spec }

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.TiesLat
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem mono_from_one (w : ℕ → ℤ) (hw : ∀ i, 1 ≤ i → w i ≤ w (i + 1)) (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    w a ≤ w b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (hw n (ha.trans hn))

theorem liftWt_antitone (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j : ℕ) (hl : Antitone lam)
    (h1 : -(lam (Fin.last m)) ≤ w 1) (hw : ∀ i, 1 ≤ i → w i ≤ w (i + 1)) : Antitone (G.liftWt t m lam w j) := by
  intro a b hab
  have hab' : a.val ≤ b.val := hab
  unfold G.liftWt
  by_cases ha : a.val < m + 1
  · by_cases hb : b.val < m + 1
    · rw [dif_pos ha, dif_pos hb]
      exact hl hab'
    · rw [dif_pos ha, dif_neg hb]
      have e1 : lam (Fin.last m) ≤ lam ⟨a.val, ha⟩ := hl (Fin.le_last _)
      have e2 := mono_from_one w hw 1 ((b.val - (m + 1)) / (t + 1) + 1) le_rfl (Nat.le_add_left _ _)
      linarith
  · have hb : ¬ b.val < m + 1 := by omega
    rw [dif_neg ha, dif_neg hb]
    have e2 := mono_from_one w hw ((a.val - (m + 1)) / (t + 1) + 1) ((b.val - (m + 1)) / (t + 1) + 1)
      (Nat.le_add_left _ _) (Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right hab' _)) 1)
    linarith

def tCo (D : D7) (τ : D.what₂.Tau) : G.HH D := D.R.iotaInv ((D.eTau τ : D.R.GG)).2

theorem coordinate_of_first_embedding (D : D7) (τ : D.what₂.Tau) (t : G.HH D) (h : (D.eTau τ : D.R.GG) = D.R.tau1 t) :
    tCo D τ = t := by
  unfold tCo
  rw [h]
  rfl

theorem tau_top_places_iff (D : D7) (t : G.HH D) : D.R.tau1 t ∈ D.host.topPlaces ↔ t ∈ D.host.TT := by
  rw [← plGG_false, plGG_top_iff]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

structure LatHyp {D : D7} (hT : GatTies D) {L : SizeData₂ D} (X : G.Inst D L) where
  vOf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    G.HH D → Fin (D.gat u w hg).P.nV
  inj : ∀ u w hg, Set.InjOn (vOf u w hg) (G.reps X (D.what₂.places.resChar w))
  n_eq : ∀ u w hg, ∀ t0 ∈ G.reps X (D.what₂.places.resChar w),
    (D.gat u w hg).P.n' (vOf u w hg t0) = addOrderOf (G.hP D (D.what₂.places.resChar w))
  pos : ∀ u w hg, ∀ t0 ∈ G.reps X (D.what₂.places.resChar w), ∀ s : Fin ((D.gat u w hg).P.n' (vOf u w hg t0)),
    ((D.eTau (hT.gat_pos u w hg ⟨vOf u w hg t0, s⟩) : D.R.Psi) : D.R.GG) =
      D.R.tau1 (t0 + s.val • G.hP D (D.what₂.places.resChar w))
  r_eq : ∀ u w hg, (D.gat u w hg).P.r =
    (if ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k then G.rG L.sc else 1)
  c : ℕ
  c_le : (c : ℝ) ≤ G.cG L
  wZ : D.what₂.Tau → ℕ → ℤ
  wZ_eq : ∀ τ, ∀ j ∈ SizeData₂.lifts D, (wZ τ j : ℝ) = wj D j τ - G.kaJ D j
  wZ_mono : ∀ τ j, 1 ≤ j → wZ τ j ≤ wZ τ (j + 1)
  base_top : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (t : D.host.TT),
    ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau1 t →
    (D.gat u w hg).P.lam0 v s 0 = L.aT t ∧ (D.gat u w hg).P.lam0 v s (Fin.last _) = -L.bT t ∧
      ∀ i : Fin ((D.gat u w hg).P.m + 1), 0 < i.val → i.val < (D.gat u w hg).P.m →
        |(D.gat u w hg).P.lam0 v s i| ≤ c
  base_off : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)),
    ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) ∉ D.host.topPlaces →
    ∀ i, |(D.gat u w hg).P.lam0 v s i| ≤ c
  wZ_ge : ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)),
    max (c : ℤ) (-((D.gat u w hg).P.lam0 v s (Fin.last _))) ≤ wZ (hT.gat_pos u w hg ⟨v, s⟩) 1

namespace LatHyp

variable {D : D7} {hT : GatTies D} {L : SizeData₂ D} {X : G.Inst D L} (H : LatHyp hT X)

open Classical in

def fills (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : G.Fills (D.gat u w hg) where
  TT := fun v => Finset.univ.filter
    (fun s => ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces)
  a := fun v s => G.aL L (tCo D (hT.gat_pos u w hg ⟨v, s⟩))
  b := fun v s => G.bL L (tCo D (hT.gat_pos u w hg ⟨v, s⟩))
  c := H.c
  base := fun v s => by
    constructor
    · intro hs
      have hs' := (Finset.mem_filter.1 hs).2
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 hs'
      have h1 := H.base_top u w hg v s ⟨t, ht⟩ hte.symm
      have h2 := coordinate_of_first_embedding D _ t hte.symm
      refine ⟨?_, ?_, h1.2.2⟩
      · rw [h1.1]
        show L.aT ⟨t, ht⟩ = G.aL L (tCo D (hT.gat_pos u w hg ⟨v, s⟩))
        rw [h2]
        unfold G.aL
        rw [dif_pos ht]
      · rw [h1.2.1]
        show -L.bT ⟨t, ht⟩ = -G.bL L (tCo D (hT.gat_pos u w hg ⟨v, s⟩))
        rw [h2]
        unfold G.bL
        rw [dif_pos ht]
    · intro hs
      exact H.base_off u w hg v s (fun h => hs (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  t := D.R.t
  mm := D.R.m
  w := fun v j s => H.wZ (hT.gat_pos u w hg ⟨v, s⟩) j
  w_ge := fun v s => H.wZ_ge u w hg v s
  w_mono := fun v s j hj => H.wZ_mono _ j hj
  domJ := fun j v s => liftWt_antitone _ _ _ _ j ((D.gat u w hg).P.dom v s)
    ((le_max_right _ _).trans (H.wZ_ge u w hg v s)) (fun i hi => H.wZ_mono _ i hi)

def latInst : G.LatInst D where
  vOf := H.vOf
  Fl := H.fills
  Lv := fun _ _ _ => { compS := fun _ => Empty, levS := fun _ c => c.elim }
  Ch := fun _ _ _ => { Kz := fun _ => 0 }
  Vram := fun _ _ _ => ⊥

theorem latTied
    (hf : ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × G.HH D),
      (D.eTau τ : D.R.GG) = G.plGG D z → G.fill X (G.bL L) j z = wj D j τ) :
    G.LatTied hT X H.latInst := by
  intro u w hg
  refine ⟨rfl, rfl, H.c_le, H.r_eq u w hg, H.inj u w hg, fun v s t ht => ⟨fun hs => ?_, fun j hj => ?_⟩,
    fun t0 ht0 => ⟨H.n_eq u w hg t0 ht0, fun s => ?_⟩⟩
  · have h1 : D.R.tau2 t ∈ D.host.topPlaces := ht ▸ (Finset.mem_filter.1 hs).2
    rw [← plGG_true, plGG_top_iff] at h1
    exact Bool.noConfusion h1.1
  · show ((H.wZ (hT.gat_pos u w hg ⟨v, s⟩) j : ℤ) : ℝ) = _
    rw [H.wZ_eq _ j hj]
    unfold G.fillG
    rw [hf j hj (hT.gat_pos u w hg ⟨v, s⟩) (true, t) (by rw [ht, plGG_true])]
  have hp := H.pos u w hg t0 ht0 s
  have hmem : s ∈ (H.latInst.Fl u w hg).TT (H.latInst.vOf u w hg t0) ↔
      t0 + s.val • G.hP D (D.what₂.places.resChar w) ∈ D.host.TT := by
    rw [← tau_top_places_iff, ← hp]
    exact ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩
  refine ⟨hp, hmem, fun _ => ⟨?_, ?_⟩, fun j hj => ?_⟩
  · exact congrArg (G.aL L) (coordinate_of_first_embedding D _ _ hp)
  · exact congrArg (G.bL L) (coordinate_of_first_embedding D _ _ hp)
  · show ((H.wZ (hT.gat_pos u w hg ⟨H.vOf u w hg t0, s⟩) j : ℤ) : ℝ) = _
    rw [H.wZ_eq _ j hj]
    unfold G.fillG
    rw [hf j hj (hT.gat_pos u w hg ⟨H.vOf u w hg t0, s⟩) (false, _) (by rw [hp, plGG_false])]

end LatHyp

theorem sizeDataLat_of_subsingleton {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts)
    (hs : ∀ u w hg, Subsingleton (D.gat u w hg).Fn) (hl : ∀ u w, L.lenMN u w = 0) (w : D.what₂.places.Pl) :
    G.LatticeLengthsAtPlace X Y K w := by
  refine ⟨fun _ u hg => ⟨0, ?_, by rw [hl]; simp⟩, fun u _ _ => hl u w⟩
  have := hs u w hg
  rw [Nat.cast_zero, Module.length_eq_zero_iff]
  infer_instance

theorem sizeDataLat_of_M_bot {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts)
    (hM : ∀ u w hg, (D.gat u w hg).M = ⊥) (hl : ∀ u w, L.lenMN u w = 0) (w : D.what₂.places.Pl) :
    G.LatticeLengthsAtPlace X Y K w := by
  refine ⟨fun _ u hg => ⟨0, ?_, by rw [hl]; simp⟩, fun u _ _ => hl u w⟩
  have h1 : (D.gat u w hg).M ⊓ Y.Vram u w hg = ⊥ := by rw [hM, bot_inf_eq]
  have h2 : Subsingleton ↥((D.gat u w hg).M ⊓ Y.Vram u w hg) := by
    rw [h1]
    infer_instance
  rw [Nat.cast_zero, Module.length_eq_zero_iff]
  infer_instance

theorem sizeDataLat_of_Vram_bot {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts)
    (hV : ∀ u w hg, Y.Vram u w hg = ⊥) (hl : ∀ u w, L.lenMN u w = 0) (w : D.what₂.places.Pl) :
    G.LatticeLengthsAtPlace X Y K w := by
  refine ⟨fun _ u hg => ⟨0, ?_, by rw [hl]; simp⟩, fun u _ _ => hl u w⟩
  have h1 : (D.gat u w hg).M ⊓ Y.Vram u w hg = ⊥ := by rw [hV, inf_bot_eq]
  have h2 : Subsingleton ↥((D.gat u w hg).M ⊓ Y.Vram u w hg) := by
    rw [h1]
    infer_instance
  rw [Nat.cast_zero, Module.length_eq_zero_iff]
  infer_instance

end Formalism.MainNotions.Inhab

end
end

