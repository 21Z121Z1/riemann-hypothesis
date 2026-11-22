import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfChChartsCover
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0003
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
import Formalism.LocalToGlobal.HermitianColumns.Bundle0002
import Formalism.LocalToGlobal.HermitianColumns.TiedQC
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0002
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0004

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelWithoutExtraPlaces
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

def levelWithoutExtraPlaces {S : HSpace E} {T f : ℕ} (X : Formalism.L2.Herm.StepLevel sp.cm S gp T f) :
    Formalism.L2.Herm.StepLevelQ sp.cm S gp T f ∅ where
  Lb := X.Lb
  Lb_fin := X.Lb_fin
  Lb_span := X.Lb_span
  Lb_int := X.Lb_int
  Lb_dual := X.Lb_dual
  Lb_index := X.Lb_index
  Uloc := X.Uloc
  Uloc_lev := X.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT _ => X.Uloc_hyp v h0 h1 hT
  Uloc_g := X.Uloc_g
  UlocAlt := X.UlocAlt
  Uloc_Q := fun v hv => absurd hv (Finset.notMem_empty v)
  U := X.U
  U_eq := X.U_eq

structure StepX (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (T f i : ℕ) where

  Q : Finset (HeightOneSpectrum (𝓞 F))
  Q_p : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal
  Q_g : ∀ v ∈ Q, ∀ a, (gp a : 𝓞 F) ∉ v.asIdeal
  prime_not_mem_places : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal

  lev : Formalism.L2.Herm.StepLevelQ sp.cm (sp.X i) gp T f Q

  HG : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin (sp.X i).rank) (resV F v))

  atG : LevAtGH sp.cm.sig (sp.X i).gram gp L.splitG lev.Lb lev.Uloc HG

  lamG : ∀ a v h, HG a v h →* Z

  typQ : ∀ v, v ∈ Q → (lev.Uloc v →* Z)

  fr : FrS I lev.Lb

  fin : Finite (ClassSet (Formalism.L2.Herm.UFin sp.cm (sp.X i)) (lev.U.subgroupOf (Formalism.L2.Herm.UAf sp.cm (sp.X i))))

def StepX.type {I : LocId L p nV W Qq} {Z : Type} [CommGroup Z] {T f i : ℕ} (Sx : StepX I Z T f i)
    (hg : ∀ a, gp a ≠ 0) (hp : ∀ a, Nat.Coprime p (gp a)) :
    awayG sp.cm.sig (sp.X i).gram Sx.lev.Uloc p →* Z :=
  Sx.atG.typeX hg Sx.lamG p hp * lamQG sp.cm.sig (sp.X i).gram Sx.lev.Uloc Sx.Q Sx.typQ p Sx.Q_p

def StepX.toStepAt {I : LocId L p nV W Qq} {O : Type} [CommRing O] {T f i : ℕ} (Sx : StepX I Oˣ T f i)
    (hg : ∀ a, gp a ≠ 0) (hp : ∀ a, Nat.Coprime p (gp a)) : StepAt I O (sp.X i).rank where
  J := (sp.X i).gram
  Lb := Sx.lev.Lb
  Uloc := Sx.lev.Uloc
  fr := Sx.fr
  ψ := (Sx.type hg hp)⁻¹
  eps := 1
  fin := finite_compG sp.cm.sig (sp.X i).gram Sx.lev.Uloc p Sx.lev.U (fun x hx => (Sx.lev.U_eq x).1 hx) Sx.fin

def StepX.ofFlag {I : LocId L p nV W Qq} {Z : Type} [CommGroup Z] {T f i : ℕ}
    (Q : Finset (HeightOneSpectrum (𝓞 F))) (Q_p : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (Q_g : ∀ v ∈ Q, ∀ a, (gp a : 𝓞 F) ∉ v.asIdeal) (prime_not_mem_places : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal)
    (lev : Formalism.L2.Herm.StepLevelQ sp.cm (sp.X i) gp T f Q)
    (atG : LevAtG sp.cm.sig (sp.X i).gram gp L.splitG lev.Lb lev.Uloc R.k R.m R.t i) (ch : CharsG F gp Z)
    (typQ : ∀ v, v ∈ Q → (lev.Uloc v →* Z)) (fr : FrS I lev.Lb)
    (fin : Finite (ClassSet (Formalism.L2.Herm.UFin sp.cm (sp.X i)) (lev.U.subgroupOf (Formalism.L2.Herm.UAf sp.cm (sp.X i))))) :
    StepX I Z T f i where
  Q := Q
  Q_p := Q_p
  Q_g := Q_g
  prime_not_mem_places := prime_not_mem_places
  lev := lev
  HG := fun _ v _ => JXbar (resV F v) (sp.X i).rank R.k R.m R.t i
  atG := atG.toH
  lamG := ch.lamX (sp.X i).rank R.k R.m R.t i
  typQ := typQ
  fr := fr
  fin := fin

end Generic

section Record

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem rank_step (D : D7) (i : ℕ) (hi : i < D.R.m) :
    D.R.k - 1 + (i + 1) * (D.R.t + 1) + 1 = (D.sp.X (i + 1)).rank := by
  rw [D.sp.X_rank (i + 1) hi]
  have := k_pred D.R
  simp only [Ranks.N]
  omega

abbrev levelsRec (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hc : CloudBound D u c)
    (hg : ∀ a, D.host.g a ≠ 0) (hp : ∀ a, Nat.Coprime p (D.host.g a))
    (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
    (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I Oˣ (D.mem u).A.T D.R.f (i + 1)) :
    Levels (fillsRec D u h hS r L I ψ y e c hc) :=
  levelsOfCh hS r (fun v s => lamRec D u (posG (zPsi D.R.toFrame h) ⟨v, s⟩)) (fun _ _ => lamRec_anti D u _) (k_pred D.R) I ψ y e
    (fillsRec D u h hS r L I ψ y e c hc) D.R.m (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_step D i hi) Cb
    (fun i hi β => (Sx i hi β).toStepAt hg hp)

def levelsRec_tie (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hc : CloudBound D u c)
    (hg : ∀ a, D.host.g a ≠ 0) (hp : ∀ a, Nat.Coprime p (D.host.g a))
    (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
    (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I Oˣ (D.mem u).A.T D.R.f (i + 1))
    (hy : ∀ i, (Quotient.mk'' (y i) : compL L p) = i)
    (hyp : ∀ i (w' : HeightOneSpectrum (𝓞 D.host.F)), ((p : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
      bc (prV (E := D.host.E) w') (y i : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) = 1)
    (i : ℕ) (hi : i < D.R.m) (β : Cb i hi) :
    GChartTie (gatRec_lev D u h hS r L I ψ y e hy hyp) (levelsRec D u h hS r L I ψ y e c hc hg hp Cb Sx) i
      (fun a : ((Sx i hi β).toStepAt hg hp).comp => ⟨hi, β, a⟩)
      (D.sp.X (i + 1)).gram (Sx i hi β).lev.Lb (Sx i hi β).lev.Uloc ((Sx i hi β).type hg hp)⁻¹ 1 :=
  levelsOfCh_tie hS r _ _ (k_pred D.R) I ψ y e hy hyp (fillsRec D u h hS r L I ψ y e c hc) D.R.m
    (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_step D i hi) Cb (fun i hi β => (Sx i hi β).toStepAt hg hp) i hi β

structure StepMore (D : D7) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup)
    {L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ}
    (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) where
  Q_p : ∀ v ∈ T.Q μ, ((p : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal
  Q_g : ∀ v ∈ T.Q μ, ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal
  prime_not_mem_places : ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal
  HG : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin (D.sp.X i).rank) (resV D.host.F v))
  atG : LevAtGH D.sp.cm.sig (D.sp.X i).gram D.host.g L.splitG (T.lev u μ i h1 hm β).Lb (T.lev u μ i h1 hm β).Uloc HG
  lamG : ∀ a v h, HG a v h →* Z
  typQ : ∀ v, v ∈ T.Q μ → ((T.lev u μ i h1 hm β).Uloc v →* Z)
  fr : FrS I (T.lev u μ i h1 hm β).Lb

def stepXTw (D : D7) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    {L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ}
    (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i)
    (M : StepMore D T u μ I Z i h1 hm β) : StepX I Z (D.mem u).A.T D.R.f i where
  Q := T.Q μ
  Q_p := M.Q_p
  Q_g := M.Q_g
  prime_not_mem_places := M.prime_not_mem_places
  lev := T.lev u μ i h1 hm β
  HG := M.HG
  atG := M.atG
  lamG := M.lamG
  typQ := M.typQ
  fr := M.fr
  fin := T.finite_cls u μ hμ i h1 hm β

abbrev levelsTw (D : D7) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hc : CloudBound D u c)
    (hg : ∀ a, D.host.g a ≠ 0) (hp : ∀ a, Nat.Coprime p (D.host.g a))
    (M : ∀ i (hi : i < D.R.m) (β : T.Ch u μ (i + 1)),
      StepMore D T u μ I Oˣ (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) hi β) :
    Levels (fillsRec D u h hS r L I ψ y e c hc) :=
  levelsRec D u h hS r L I ψ y e c hc hg hp (fun i _ => T.Ch u μ (i + 1))
    (fun i hi β => stepXTw D T u μ hμ I Oˣ (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) hi β (M i hi β))

end Record

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelCharts.ToFSSymmStab
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

structure StepG (I : LocId L p nV W Qq) (N : ℕ) where
  J : Matrix (Fin N) (Fin N) E
  hJ : IsHerm (sp.cm.sig : E →+* E) J
  hdet : IsUnit J.det
  Lb : Submodule (𝓞 E) (Fin N → E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))
  fr : FrS I Lb
  U : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

variable {I : LocId L p nV W Qq} {N : ℕ}

def StepG.uGL (S : StepG I N) (v : Fin nV) :
    UPts sp.cm.sig S.J ((I.plc v).adicCompletion F) ≃* GL (Fin N) ((I.plc v).adicCompletion F) :=
  locGL sp.cm.sig S.J S.hJ S.hdet _ (I.spl (I.plc v) (I.pl v).2) (I.spl_sig (I.plc v) (I.pl v).2)

def jPS (S : StepG I N) :
    (∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F)) →* UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F) :=
  (secAll F E sp.cm.sig S.J I.plc I.plc_inj).comp
    (MonoidHom.pi fun v => (S.uGL v).symm.toMonoidHom.comp (Pi.evalMonoidHom _ v))

theorem jPS_at (S : StepG I N) (g : ∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F)) (v : Fin nV) :
    bc ((RingHom.fst _ _).comp (I.spl (I.plc v) (I.pl v).2).toRingHom)
      (bc (prV (E := E) (I.plc v)) (jPS S g : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) = g v := by
  show bc _ (bc (prV (E := E) (I.plc v)) (secAll F E sp.cm.sig S.J I.plc I.plc_inj _ : GL (Fin N) _)) = g v
  rw [bc_secAll_same]
  have := locGL_apply sp.cm.sig S.J S.hJ S.hdet _ (I.spl (I.plc v) (I.pl v).2)
    (I.spl_sig (I.plc v) (I.pl v).2) ((S.uGL v).symm (g v))
  exact this.symm.trans ((S.uGL v).apply_symm_apply (g v))

theorem jPS_off (S : StepG I N) (g : ∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F))
    (w' : HeightOneSpectrum (𝓞 F)) (hw : ((p : ℕ) : 𝓞 F) ∉ w'.asIdeal) :
    bc (prV (E := E) w') (jPS S g : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 :=
  bc_secAll_off F E sp.cm.sig S.J I.plc I.plc_inj w' (fun v h => hw (h ▸ (I.pl v).2)) _

theorem jPS_mem_awayG (S : StepG I N) (g : ∀ v : Fin nV, GL (Fin N) ((I.plc v).adicCompletion F)) :
    (jPS S g : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ awayG sp.cm.sig S.J S.Uloc p := by
  refine (mem_awayG sp.cm.sig S.J S.Uloc p _).2 ⟨(jPS S g).2, ?_⟩
  intro v hv
  rw [jPS_off S g v hv]
  exact Subgroup.one_mem _

abbrev frVS (S : StepG I N) (v : Fin nV) : GL (Fin N) ((I.plc v).adicCompletion F) := S.fr.fr (I.plc v) (I.pl v).2

def toFS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV) :
    GL (Fin (m + 1)) Qq ≃* GL (Fin N) ((I.plc v).adicCompletion F) :=
  ((castGL hk Qq).trans (bcE (I.eQ v))).trans (MulAut.conj (frVS S v))

theorem toFS_symm (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV)
    (X : GL (Fin N) ((I.plc v).adicCompletion F)) :
    (toFS S hk v).symm X = (castGL hk Qq).symm ((bcE (I.eQ v)).symm ((frVS S v)⁻¹ * X * frVS S v)) := rfl

abbrev GAS (S : StepG I N) : Type := UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)

def prPS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) : GAS S →* (Fin nV → GL (Fin (m + 1)) Qq) :=
  MonoidHom.pi fun v => (toFS S hk v).symm.toMonoidHom.comp
    ((bc (fstV I v)).comp ((bc (prV (E := E) (I.plc v))).comp (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)).subtype))

theorem prPS_apply (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (x : GAS S) (v : Fin nV) :
    prPS S hk x v = (toFS S hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (x : GL (Fin N) _))) := rfl

def jQS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) : (Fin nV → GL (Fin (m + 1)) Qq) →* GAS S :=
  (jPS S).comp (MonoidHom.pi fun v => (toFS S hk v).toMonoidHom.comp (Pi.evalMonoidHom _ v))

theorem prPS_jQS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (g : Fin nV → GL (Fin (m + 1)) Qq) :
    prPS S hk (jQS S hk g) = g := by
  funext v
  rw [prPS_apply]
  have := jPS_at S (fun v => toFS S hk v (g v)) v
  show (toFS S hk v).symm (bc (fstV I v) (bc (prV (E := E) (I.plc v)) (jPS S (fun v => toFS S hk v (g v)) : GL (Fin N) _))) = g v
  rw [this, MulEquiv.symm_apply_apply]

def HypAtPS (S : StepG I N) : Prop :=
  ∀ (v : Fin nV) (x : GL (Fin N) (E ⊗[F] (I.plc v).adicCompletion F)),
    x ∈ UPts sp.cm.sig S.J ((I.plc v).adicCompletion F) →
    (x ∈ S.Uloc (I.plc v) ↔
      (∀ a b, (((frVS S v)⁻¹ * bc (fstV I v) x * frVS S v : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frVS S v)⁻¹ * bc (fstV I v) x * frVS S v)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F)

theorem toFS_symm_stab (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (v : Fin nV)
    (X : GL (Fin N) ((I.plc v).adicCompletion F)) :
    (toFS S hk v).symm X ∈ stabStd (k := m + 1) (Qq := Qq) W ↔
      (∀ a b, (((frVS S v)⁻¹ * X * frVS S v : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F) ∧
      ∀ a b, ((((frVS S v)⁻¹ * X * frVS S v)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) a b ∈
        (I.plc v).adicCompletionIntegers F := by
  rw [stabStd_iff, ← map_inv, toFS_symm, toFS_symm]
  have key : ∀ M : GL (Fin N) ((I.plc v).adicCompletion F),
      (∀ a b, ((castGL hk Qq).symm ((bcE (I.eQ v)).symm M) : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b ∈
        (algebraMap W Qq).range) ↔ ∀ a b, (M : Matrix (Fin N) (Fin N) _) a b ∈ (I.plc v).adicCompletionIntegers F := by
    intro M
    have h1 : ∀ a b, ((castGL hk Qq).symm ((bcE (I.eQ v)).symm M) : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b ∈
        (algebraMap W Qq).range ↔ (M : Matrix (Fin N) (Fin N) _) (Fin.cast hk a) (Fin.cast hk b) ∈
          (I.plc v).adicCompletionIntegers F := by
      intro a b
      rw [castGL_symm_apply, bcE_symm_apply]
      have := I.completion_integers_iff v ((I.eQ v).symm ((M : Matrix (Fin N) (Fin N) _) (Fin.cast hk a) (Fin.cast hk b)))
      rw [RingEquiv.apply_symm_apply] at this
      exact this
    constructor
    · intro h a b
      have := (h1 (Fin.cast hk.symm a) (Fin.cast hk.symm b)).1 (h _ _)
      simpa using this
    · intro h a b
      exact (h1 a b).2 (h _ _)
  have e : (frVS S v)⁻¹ * X⁻¹ * frVS S v = ((frVS S v)⁻¹ * X * frVS S v)⁻¹ := by group
  rw [key, e, key]

def fibPS (S : StepG I N) {m : ℕ} (hk : m + 1 = N) (hH : HypAtPS S) :
    Fib (S.U.subgroupOf (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)))
      ((awayG sp.cm.sig S.J S.Uloc p).subgroupOf (UPts sp.cm.sig S.J (FiniteAdeleRing (𝓞 F) F)))
      (stabTup (nV := nV) (k := m + 1) (Qq := Qq) W) where
  j := jQS S hk
  pr := prPS S hk
  pr_j := prPS_jQS S hk
  j_mem := fun g => Subgroup.mem_subgroupOf.2 (jPS_mem_awayG S _)
  K_iff := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, S.U_eq, mem_stabTup, mem_awayG]
    have hloc : ∀ v : Fin nV, bc (prV (E := E) (I.plc v)) (x : GL (Fin N) _) ∈ S.Uloc (I.plc v) ↔
        prPS S hk x v ∈ stabStd (k := m + 1) (Qq := Qq) W := by
      intro v
      rw [prPS_apply, toFS_symm_stab]
      exact hH v _ (Formalism.UG.P.afsplit_bc_mem sp.cm.sig S.J (I.plc v) _ x.2)
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun v _ => h2 v⟩, fun v => (hloc v).1 (h2 _)⟩
    · rintro ⟨⟨h3, h4⟩, h2⟩
      refine ⟨h3, fun v => ?_⟩
      by_cases hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal
      · obtain ⟨v', rfl⟩ : ∃ v', I.plc v' = v := ⟨I.pl.symm ⟨v, hv⟩, by simp [LocId.plc]⟩
        exact (hloc v').2 (h2 v')
      · exact h4 v hv

end Formalism.L2.G
end
end

