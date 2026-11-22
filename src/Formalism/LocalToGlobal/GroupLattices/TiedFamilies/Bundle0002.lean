import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0001
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrH
import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem selfDualAt_colLevel (L : ColLevel R F E sp gp C A clsLat) (v : HeightOneSpectrum (𝓞 F))
    (hT : (A.T : 𝓞 F) ∉ v.asIdeal) : SelfDualAt sp.cm.sig sp.gram0 v L.Lb :=
  self_dual_lattice_at F E R.k sp.cm.sig sp.gram0 v L.Lb A.T L.Lb_fin
    (fun x hx y hy => L.Lb_int y hy x hx) (fun y hy => L.Lb_dual y hy) hT

theorem selfDualAtP_of_not_mem (I : LocId L p nV W Qq) (hT : ∀ v : Fin nV, (A.T : 𝓞 F) ∉ (I.plc v).asIdeal) : Cmp.SelfDualAtP I :=
  fun v y => selfDualAt_colLevel L (I.plc v) (hT v) y

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem selfDualAtP_colLevel (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq') : Cmp.SelfDualAtP I :=
  selfDualAtP_of_not_mem I fun v => (notBad_C D u w hg I v).2.2

theorem isHyperbolicAt_rec_of_placeIdentification (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq') : Cmp.HypAtP I :=
  isHyperbolicAt_rec_of_isSelfDualAt D u w hg I (selfDualAtP_colLevel D u w hg I)

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

open Formalism.L2.Forms

def atTTSet {u : D.what₂.Word} (A : AtTTied (D := D) u) : AtTTied (D := setGat D g' hd') u := { A with }

set_option maxHeartbeats 4000000 in
def clsSet {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied (D := D) u i hi) :
    ClsTied (D := setGat D g' hd') u i hi := { K with }

set_option maxHeartbeats 4000000 in
def valSet {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied (D := D) u i hi}
    (W : ValTied (D := D) u eV i hi K) : ValTied (D := setGat D g' hd') u eV i hi (clsSet D g' hd' K) := { W with }

set_option maxHeartbeats 4000000 in
def lvSet {u : D.what₂.Word} {A : AtTTied (D := D) u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied (D := D) u A i hi) :
    LvTied (D := setGat D g' hd') u (atTTSet D g' hd' A) i hi := { P with }

set_option maxHeartbeats 4000000 in
def clsPSet {u : D.what₂.Word} (K : ClsPTied (D := D) u) : ClsPTied (D := setGat D g' hd') u := { K with }

set_option maxHeartbeats 4000000 in
def valPSet {u : D.what₂.Word} {K : ClsPTied (D := D) u} (W : ValPTied (D := D) u K) :
    ValPTied (D := setGat D g' hd') u (clsPSet D g' hd' K) := { W with }

set_option maxHeartbeats 4000000 in
def tilSet {u : D.what₂.Word} {A : AtTTied (D := D) u} {K : ClsPTied (D := D) u} {P : LvTied (D := D) u A D.R.m le_rfl}
    (Tl : TilTied (D := D) u A K P) :
    TilTied (D := setGat D g' hd') u (atTTSet D g' hd' A) (clsPSet D g' hd' K) (lvSet D g' hd' P) := { Tl with }

set_option maxHeartbeats 4000000 in
def tilAdSet {u : D.what₂.Word} {A : AtTTied (D := D) u} {K : ClsPTied (D := D) u} {P : LvTied (D := D) u A D.R.m le_rfl}
    {Tl : TilTied (D := D) u A K P} {Km : ClsTied (D := D) u D.R.m le_rfl} (Ta : TilAd (D := D) Tl Km) :
    TilAd (D := setGat D g' hd') (tilSet D g' hd' Tl) (clsSet D g' hd' Km) := { Ta with }

set_option maxHeartbeats 8000000 in

def formsSet {u : D.what₂.Word} (T : FormsTied D u) : FormsTied (setGat D g' hd') u where
  atT := atTTSet D g' hd' T.atT
  cls := fun i hi => clsSet D g' hd' (T.cls i hi)
  val := fun i hi => valSet D g' hd' (T.val i hi)
  gl := T.gl
  gl_K := T.gl_K
  glev := T.glev
  lv := fun i hi => lvSet D g' hd' (T.lv i hi)
  fMe := T.fMe
  fv := T.fv
  upN := T.upN
  dnN := T.dnN
  norm := T.norm
  bw := T.bw
  clsP := clsPSet D g' hd' T.clsP
  valP := valPSet D g' hd' T.valP
  normP := T.normP
  glevP := T.glevP
  til := tilSet D g' hd' T.til
  tilLat := T.tilLat
  tilFv := T.tilFv
  tilAd := tilAdSet D g' hd' T.tilAd
  frExt := T.frExt
  eWz := T.eWz
  evz := T.evz
  jM := T.jM
  per := T.per
  DGam := T.DGam

set_option maxHeartbeats 4000000 in

def forms0Set {u : D.what₂.Word} (T : Forms0 D u) : Forms0 (setGat D g' hd') u where
  atT := atTTSet D g' hd' T.atT
  cls0 := clsSet D g' hd' T.cls0
  val0 := valSet D g' hd' T.val0
  gl := T.gl
  gl_K := T.gl_K
  glev0 := T.glev0
  lv0 := lvSet D g' hd' T.lv0
  fMe0 := T.fMe0
  fv0 := T.fv0
  up_natural_level_zero := T.up_natural_level_zero
  down_natural_level_zero := T.down_natural_level_zero
  norm0 := T.norm0
  bw0 := T.bw0

end Formalism.L2.G
end
end

