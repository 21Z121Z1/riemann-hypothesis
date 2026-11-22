import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
section
noncomputable section

namespace GlobalTheory.Mem.Db

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  GlobalTheory.Mem.Df NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure NStd {B : Base} {C : Cols B} {W : RowsRest B C} (N : NStage B C W) : Prop where
  loc : IsEmpty N.nd.Loc
  cover : N.ntw.TwCover
  chiT : ∀ (k : Fin 2) (v : N.nd.PlG k), ∃ w : (ZMod (B.host.g k))ˣ, orderOf w = B.host.g k - 1 ∧
    ∀ j : Fin B.R.m, N.nd.chiT k v j = w ^ (2 * (j.1 + 1))

structure SStd (K : Ctx) {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) (cd : CDHaar) : Prop where
  del : S.s.Del = (Delv K.s K.cD : ℚ)
  scale : S.s.cdScale = Vol.trueScale cd
  dsig : ∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

def GCols (K : Ctx) (w : ColW B f T) (G : GJStage B w.C) : Prop :=
  ∀ W V S N, GatNum K.s (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩)

structure ZDef (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 where
  hX : B.fields.Ok
  e : ∀ a : w.C.Tup, MtCx w.I a ≃ₗ[ℂ] Z.W.Amb a
  tru : DefTrue w.I w.l hX Z.W e
  std : StandIn Z.W
  etaF : Z.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF)
  s : SStd K Z.S Z.G.cd
  n : NStd Z.N
  g : GCols K w Z.G

structure Side (w : ColW B f T) (Z : w.Lt) : Type 1 where
  th : ThetaX (w.D Z)
  th_io : th.TieIo
  nch : NChoice (w.D Z)
  n : NchT w Z ∅ nch
  xd : ThData (w.D Z)
  X : DivX (w.D Z)
  qp : TC.QpIs w.I X.Qp
  p0 : BaseLevelRowSide (w.D Z)
  amb0 : AmbForm (w.D Z) p0.s
  row : V4.RowLay (w.D Z) p0 X
  gauge : GlobalTheoryTheory.GenusMassVolumes.GaugeFam (w.D Z).host.F (w.D Z).host.E (w.D Z).sp.cm.sig
  gauge_def : gauge.IsGauge

structure CoreB (K : Ctx) (w : ColW B f T) (Z : w.Lt) : Type 1 where
  isOver : K.Over B.toPre
  untw : T = TwDat.untw B T.pl
  forced : Forced K B T
  pin : ColPin w
  z : ZDef K w Z
  mu : V4.MuIsW (w.st Z) f T ∅ w.I.xi
  sd : Side w Z
  t : ColumnDataSplitPrimes K w Z
  Gy : G.LatInst (w.D Z)
  ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy
  gy : GyLay K (w.D Z) t.Gt t.cmp Gy
  kt : KerT t.toColT sd.X Gy ker
  entC : ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (h : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs sd.X (w.tw Z)),
    kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs h
  col : ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1)
  amb : AmbForm (w.D Z) (RowSide.sharp (w.D Z))
  ambTrue : AmbTrue w.I w.l z.hX Z z.e amb
  mtStable : DQ.MtStableAt (w.D Z)
  cd : cdScaleTie (w.D Z)
  dsT : dsigTie (w.D Z)
  ds : ∀ τ, Formalism.L2.Theta.IsDsig (w.D Z) τ ((w.D Z).dsig τ)

def CoreB.obj {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : Obj2 (w.D Z) where
  gatT := b.t.Gt
  th := b.sd.th
  cmp := b.t.cmp
  tw := w.tw Z
  Gy := b.Gy
  errX := Formalism.L2.Herm.toErrXS b.t.full.1
  nch := b.sd.nch
  xd := b.sd.xd
  lev := b.t.full.1.base.lev0
  X := b.sd.X
  p0 := b.sd.p0
  ker := b.ker
  amb := b.amb
  amb0 := b.sd.amb0
  gauge := b.sd.gauge

def setDivZ {C : Cols B} (Z : TC.Later B C) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) : TC.Later B C :=
  { Z with V := { Z.V with div := (setDiv (assemble B C Z.W Z.V Z.S Z.N Z.G) N h).div } }

theorem D_setDivZ (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    w.D (setDivZ Z N h) = setDiv (w.D Z) N h := rfl

def IsB (K : Ctx) (D : D7) (O : Obj2 D) : Prop :=
  ∃ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z),
    (⟨D, O⟩ : Σ D : D7, Obj2 D) = ⟨w.D Z, b.obj⟩

def PinU : WP := fun K B f T w => Pinned K B f T w ∧ T = TwDat.untw B T.pl

def ForVol (w : ColW B f T) (P : w.Lt → Prop) : Prop :=
  ∀ (vol : HSpace B.host.E → ℝ) (cd : CDHaar), (∀ W, 0 < vol W) →
    (∀ Z : w.Lt, Z.G.vol = vol → Z.G.cd = cd → Formalism.L2.Herm.VolumeCompatible (w.D Z)) → ∃ Z : w.Lt, Z.G.vol = vol ∧ Z.G.cd = cd ∧ P Z

def HasB : WP := fun K _ _ _ w => ForVol w fun Z => Nonempty (CoreB K w Z)

theorem CoreB.isB {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : IsB K (w.D Z) b.obj := ⟨B, f, T, w, Z, b, rfl⟩

theorem IsB.ind {K : Ctx} {R : ∀ D : D7, Obj2 D → Prop}
    (h : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z), R (w.D Z) b.obj)
    {D : D7} {O : Obj2 D} (hD : IsB K D O) : R D O := by
  obtain ⟨B, f, T, w, Z, b, e⟩ := hD
  cases e
  exact h B f T w Z b

theorem IsB.ind_obj {K : Ctx} {R : ∀ D : D7, Obj D → Prop}
    (h : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z) (O : Obj (w.D Z)),
      ofObj O = b.obj → R (w.D Z) O)
    {D : D7} {O : Obj D} (hD : IsB K D (ofObj O)) : R D O :=
  IsB.ind (R := fun D O' => ∀ O : Obj D, ofObj O = O' → R D O) h hD O rfl

theorem IsB.ind_lay {K : Ctx} {R : ∀ D : D7, Lay D → Prop}
    (h : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z) (Y : Lay (w.D Z)),
      layObj Y = b.obj → R (w.D Z) Y)
    {D : D7} {Y : Lay D} (hD : IsB K D (layObj Y)) : R D Y :=
  IsB.ind (R := fun D O' => ∀ Y : Lay D, layObj Y = O' → R D Y) h hD Y rfl

theorem exists_isB_iff_coreB (K : Ctx) : (∃ (D : D7) (O : Obj2 D), IsB K D O) ↔
    ∃ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), Nonempty (CoreB K w Z) :=
  ⟨fun ⟨_, _, B, f, T, w, Z, b, _⟩ => ⟨B, f, T, w, Z, ⟨b⟩⟩, fun ⟨_, _, _, _, _, ⟨b⟩⟩ => ⟨_, _, b.isB⟩⟩

theorem CoreB.pinU {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : PinU K B f T w := ⟨⟨b.pin⟩, b.untw⟩

theorem CoreB.muAt_eq {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) (v : (w.D Z).what₂.places.Pl) :
    (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 := b.mu.off v (Set.notMem_empty v)

theorem CoreB.over {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : Over (w.D Z) K.P K.Lv := by
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := b.isOver
  exact ⟨sp, hT, hY, hA, hV, hz, w.st Z, h, rfl⟩

theorem CoreB.volTied {K : Ctx} {w : ColW B f T} {Z : w.Lt} (b : CoreB K w Z) : Formalism.L2.Herm.VolumeCompatible (w.D Z) := b.t.full.1.vol

theorem ForVol.mono {w : ColW B f T} {P Q : w.Lt → Prop} (h : ForVol w P) (hPQ : ∀ Z, P Z → Q Z) : ForVol w Q :=
  fun vol cd hp ht => let ⟨Z, a, b, p⟩ := h vol cd hp ht; ⟨Z, a, b, hPQ Z p⟩

theorem HasB.forVol_isB {K : Ctx} {w : ColW B f T} (h : HasB K B f T w) : ForVol w fun Z => ∃ O, IsB K (w.D Z) O :=
  ForVol.mono h fun _ ⟨b⟩ => ⟨_, b.isB⟩

section Layers

variable {K : Ctx} {w : ColW B f T} {Z : w.Lt}

def CoreB.lay (b : CoreB K w Z) (hv : StandardLattice.VolumeEqMass₂ (w.D Z)) : Lay (w.D Z) :=
  { b.obj with
    ties := ⟨b.cd, b.dsT, b.sd.row.bu_def, twCoverPair_of_tie _ _ b.sd.n.tie, B.coeffGaloisSubfield_isGalois, b.sd.row.ft_occ⟩
    rrDef := b.sd.row.rrDef
    th_io := b.sd.th_io
    vram := b.gy.vram
    fills_all := b.gy.fills
    idx := b.sd.row.idx
    kap_def := b.sd.row.kap_def
    lam_def := b.sd.row.lam_def
    kapR_def := b.sd.row.kapR_def
    piG_lev := b.col.piG_lev
    piT_lev := b.col.piT_lev
    seen := b.col.seen
    tauOf := b.col.tauOf
    dgam := fun u μ => ⟨fun u' μ' i hi x => by
      rw [b.col.one u μ, ← b.col.one u' μ']
      exact ((w.D Z).chTw u' μ').dvd_DGam i hi x, b.col.one u μ⟩
    nch_tie := b.sd.n.tie
    rationalRoots_def := b.sd.row.rationalRoots_def
    duStar_def := (sizes_eq_count K (w.st Z) b.isOver hv b.z.s.dsig).1
    Dstar_def := (sizes_eq_count K (w.st Z) b.isOver hv b.z.s.dsig).2
    gauge_def := b.sd.gauge_def }

theorem CoreB.layObj_lay (b : CoreB K w Z) (hv : StandardLattice.VolumeEqMass₂ (w.D Z)) : layObj (b.lay hv) = b.obj := rfl

theorem CoreB.isB_lay (b : CoreB K w Z) (hv : StandardLattice.VolumeEqMass₂ (w.D Z)) : IsB K (w.D Z) (layObj (b.lay hv)) := b.isB

theorem CoreB.tupUsed (b : CoreB K w Z) : DQ.TupUsedAt (w.D Z) := by
  intro μ
  have hμ : w.I.xi μ ∈ T.set f := b.mu.range ▸ Set.mem_range_self μ
  rcases hμ with (h | h | h) | ⟨v, h⟩
  · exact .inl (b.mu.inj (h.trans b.mu.mu0.symm))
  · exact .inr (.inl (b.mu.inj (h.trans b.mu.star.symm)))
  · exact .inr (.inr (.inl (b.mu.inj (h.trans b.mu.star'.symm))))
  · unfold TwDat.xiTw at h
    rw [b.mu.supp v (Set.notMem_empty v), mul_one] at h
    split_ifs at h
    · exact .inr (.inr (.inl (b.mu.inj (h.symm.trans b.mu.star'.symm))))
    · exact .inr (.inl (b.mu.inj (h.symm.trans b.mu.star.symm)))

theorem ev_recOK : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), CoreB K w Z →
    RecOK K.s K.C K.cD (w.D Z) :=
  LayOfCore.ev_imp TamePow.tame_of_pow fun _ hK _ _ _ w Z b =>
    ⟨b.z.s.del, b.z.etaF, fun v hv j h1 h2 => by
        have a := b.sd.row.untw v hv j h1 h2
        have c := b.sd.row.untw ((w.D Z).what₂.places.conj v) (b.muAt_eq _) j h1 h2
        unfold Rows.Data.Aj
        rw [hv, a.1, a.2, c.1]
        rfl,
      Set.finite_empty.subset fun v hv => (hv (b.muAt_eq v)).elim, (Full.dgam_pos_and_full _).1, (Full.dgam_pos_and_full _).2,
      hK (w.st Z) b.isOver b.z.n.chiT, b.col.mink, b.col.atT⟩

theorem CoreB.led (b : CoreB K w Z) (L : SizeData₂ (w.D Z)) (hs : L.sc = K.s) (hW : WtEq L K.a K.b) (hV : Val K.C K.cD K.ch L)
    (X : G.Inst (w.D Z) L) (hX : CanonInst X) (he : G.EpDef X K.C.cX.Ce) (hk : G.KapIDef X K.C.GK)
    (hf : ∀ v, G.ParametersFill X K.C.GK v) :
    G.LatTied b.obj.gatT X b.obj.Gy ∧ EpTie X ∧
      ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        (∀ x, b.obj.cmp.cmp u v hg ((w.D Z).nuIn u x) ∈ G.NP X b.obj.Gy K.C.GK u v hg →
          InLoc ((w.D Z).plEq v) (DV.MramL (w.D Z) u) x) ∧
        ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ DV.MramL (w.D Z) u,
          b.obj.cmp.cmp u v hg ((w.D Z).nuIn u (n • x)) ∈ G.NP X b.obj.Gy K.C.GK u v hg := by
  refine ⟨b.gy.led L hs hW hV X hX he hk hf, fun u v hg => ?_, fun u v hg =>
    NP_full (w.D Z) L X b.Gy K.C.GK b.t.cmp b.gy.vram u v hg⟩
  have hC : K.C.cX.Ce = 1 := by
    have := K.std.1
    unfold FC.Fixed at this
    tauto
  rw [((b.z.g Z.W Z.V Z.S Z.N).1 u v hg).2, he, hC, hs]

end Layers

example {K : Ctx} {D : D7} {O : Obj2 D} (h : IsB K D O) (v : D.what₂.places.Pl) : D.what₂.muAt v = D.what₂.mu0 :=
  IsB.ind (R := fun D _ => ∀ v, D.what₂.muAt v = D.what₂.mu0) (fun _ _ _ _ _ b => b.muAt_eq) h v

example {C : Cols B} (Z : TC.Later B C) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) :
    (setDivZ Z N h).G = Z.G ∧ (setDivZ Z N h).V.div.h = h := ⟨rfl, rfl⟩

example (w : ColW B f T) (vol : HSpace B.host.E → ℝ) (cd : CDHaar) (hp : ∀ W, 0 < vol W)
    (ht : ∀ Z : w.Lt, Z.G.vol = vol → Z.G.cd = cd → Formalism.L2.Herm.VolumeCompatible (w.D Z)) : ¬ ForVol w fun _ => False :=
  fun h => let ⟨_, _, _, p⟩ := h vol cd hp ht; p

end GlobalTheory.Mem.Db

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsTiedOfIsRecG
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.LayerTwoModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

open Formalism.MainNotions.G Formalism.UG Formalism.L2.Forms Formalism.L2.G

theorem isRecG_retie {sc D Gt c H F} (h : IsRecG sc D Gt c H F) (g') : IsRecG sc D Gt c ⟨H.lev0, g'⟩ F := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨D0, Lc, I, ψ, hd, ⟨_, g'⟩, hL, _, B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩

theorem gatNum_of_isRecG {sc D Gt c H F} (h : IsRecG sc D Gt c H F) : GatNum sc D := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  intro u w hg
  exact ⟨rfl, rfl⟩

theorem exists_tied_of_isRecG {sc D Gt c H F} (h : IsRecG sc D Gt c H F) :
    ∃ g : GroupCompatibilityAll D Gt c, g.herm.lev0 = H.lev0 ∧ g.forms = F ∧ IsRecG sc D Gt c g.herm g.forms := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  exact ⟨groupCompatibilityOfRecursion D0 sc 1 Lc I ψ hd _ hL _ B hBs hB (CH.toHyp0 fun u w hg v s x =>
      pos_C D0 sc 1 Lc I ψ hd _ hL B hBs hB iK lam hK hPos u w hg v s x).toHyp fun u w h => isHyperbolicAt_rec_of_placeIdentification D0 u w h (I u w h),
    rfl, rfl, isRecG_retie ⟨D0, Lc, I, ψ, hd, _, hL, _, B, hBs, hB, iK, lam, hK, hPos, CH, rfl⟩ _⟩

section Stages
variable {B : Base} {C : Cols B} (W W' : RowsRest B C) (V : DivStage B C W) (V' : DivStage B C W') (S : SStage B C W)
  (S' : SStage B C W') (N : NStage B C W) (N' : NStage B C W') (G G' : GJStage B C)

theorem hP_assemble_eq (p) : hP (assemble B C W V S N G) p = hP (assemble B C W' V' S' N' G') p := rfl

theorem lamRec_stages (u g) : lamRec (assemble B C W V S N G) u g = lamRec (assemble B C W' V' S' N' G') u g := rfl

theorem tauRec_stages (w : B.places.Pl) [h : Fact (B.places.resChar w).Prime] (n) :
    @tauRec (assemble B C W V S N G) w h n = @tauRec (assemble B C W' V' S' N' G') w h n := rfl

theorem omTied_stages (δ : ℂ) :
    Formalism.L2.GlobalTheoryTheory.OmegaCompatible (assemble B C W V S N G) δ ↔ Formalism.L2.GlobalTheoryTheory.OmegaCompatible (assemble B C W' V' S' N' G) δ := Iff.rfl

end Stages

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem above_auto (w : ColW B f T) (v) : w.I.sel v ∈ aboveF (L := B.host.E) B.host.F v := by
  rw [aboveF, Set.Finite.mem_toFinset]
  exact HeightOneSpectrum.ext (w.ok.sel_ok v)

theorem vals_auto (w : ColW B f T) (a P) : ∃ z : B.LL, B.embLL z = (((w.I.xi a).val P : ℂˣ) : ℂ) :=
  ⟨_, (w.ok.xi_reads a _).symm⟩

theorem roots_auto (w : ColW B f T) (ht : TC.IsTw w.I) (a) (P) (hP : P ∈ w.I.Q a) :
    ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal)) := by
  classical
  obtain ⟨z, hz⟩ := TC.root_of_ok w.ok ht.deep a ⟨P, Finset.mem_union_right _ hP⟩ (TC.Q_notMem_of_ok w.ok a P hP)
  have hq : (Formalism.L2.Col.qOf P : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  have hq0 : Formalism.L2.Col.qOf P ≠ 0 := Nat.cast_ne_zero.1 hq
  have h1 := Complex.isPrimitiveRoot_exp (Formalism.L2.Col.qOf P ^ (2 * B.R.m)) (pow_ne_zero _ hq0)
  rw [← hz] at h1
  have h2 : IsPrimitiveRoot z (Formalism.L2.Col.qOf P ^ (2 * B.R.m)) := h1.of_map_of_injective w.I.glob.σ₀.injective
  have hm : 2 * B.R.m = (2 * B.R.m - 1) + 1 := by have := B.R.two_le_m; omega
  have h3 := h2.pow (Nat.pos_of_ne_zero (pow_ne_zero _ hq0)) (a := Formalism.L2.Col.qOf P ^ (2 * B.R.m - 1)) (b := Formalism.L2.Col.qOf P)
    (by conv_lhs => rw [hm, pow_succ])
  exact ⟨_, h3⟩

theorem exists_over (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ v.asIdeal := by
  have hu : ¬ IsUnit (p : 𝓞 L) := fun h => by
    have h1 := h.map (Algebra.norm ℤ)
    rw [show (p : 𝓞 L) = algebraMap ℤ (𝓞 L) p by simp, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne',
      Int.isUnit_iff_natAbs_eq] at h1
    exact hp.one_lt.ne' (by simpa using h1)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 L)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hp' : (p : 𝓞 L) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => hp.ne_zero (by rw [h] at hp'; exact_mod_cast (Ideal.mem_bot.1 hp'))⟩, hp'⟩

theorem under_mem (w : ColW B f T) {p : ℕ} {v : HeightOneSpectrum (𝓞 B.host.F)} (hv : (p : 𝓞 B.host.F) ∈ v.asIdeal) :
    (p : 𝓞 B.host.K) ∈ ((show HeightOneSpectrum (𝓞 B.host.E) from w.I.sel v).under (𝓞 B.host.K)).asIdeal := by
  have h := w.ok.sel_ok v
  rw [← h] at hv
  have h1 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (p : 𝓞 B.host.F) ∈ (w.I.sel v).asIdeal := hv
  show algebraMap (𝓞 B.host.K) (𝓞 B.host.E) (p : 𝓞 B.host.K) ∈ (w.I.sel v).asIdeal
  rw [map_natCast] at h1 ⊢
  exact h1

theorem pinned_iff (w : ColW B f T) : Pinned K B f T w ↔ TC.IsTw w.I ∧ ColIn.JetsIn w.I ∧ Half B w.I.sel := by
  refine ⟨fun ⟨p⟩ => ⟨p.isTw, p.jets, p.half⟩, fun ⟨a, b, c⟩ => ?_⟩
  obtain ⟨v₀, h₀⟩ := exists_over B.host.F B.host.pde_prime
  obtain ⟨v₁, h₁⟩ := exists_over B.host.F B.host.pde'_prime
  exact ⟨⟨a, b, (base_fields_primes_ok B w.px).1, above_auto w, c,
    ⟨_, _, under_mem w h₀, under_mem w h₁, fun v _ => w.I.sel v, fun v _ => w.I.sel v,
      fun v hv => ⟨above_auto w v, c v v₀ _ B.host.pde_prime hv h₀⟩,
      fun v hv => ⟨above_auto w v, c v v₁ _ B.host.pde'_prime hv h₁⟩⟩,
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun a P _ => vals_auto w a P, roots_auto w a⟩⟩

theorem gIs2_iff (w : ColW B f T) (G : GJStage B w.C) : GIs2 K w G ↔
    ∀ W V S N, Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, G⟩) ∧ Nonempty (ColumnDataSplitPrimes K w ⟨W, V, S, N, G⟩) :=
  ⟨fun h W V S N => ⟨(h W V S N).1, (h W V S N).2.2⟩,
    fun h W V S N => let ⟨a, ⟨t⟩⟩ := h W V S N; ⟨a, gatNum_of_isRecG t.isRec, ⟨t⟩⟩⟩

theorem cond_eq_of_twisted {w : ColW B f T} {Z : w.Lt} {Wt} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (v)
    (hv : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0) : nch.Q v = T.Q v := by
  have h1 := (n.tp.psi_is v hv).ram
  rw [n.psi] at h1
  ext P
  have := (h1 P).symm.trans ((T.psi_is v).ram P)
  exact not_iff_not.1 this

end GlobalTheory.Mem.Top.Bl.LayerTwoModel

end
end

