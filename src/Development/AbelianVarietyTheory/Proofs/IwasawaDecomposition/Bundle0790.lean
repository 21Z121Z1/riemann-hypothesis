import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0765
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0753
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0771
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

section Gen

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem eigAd_of {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {Sb eig} (h : EigAd Y Sb eig)
    (v : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) → (R.HW i (sg0 D A3.A)).H) (H : ∀ i y, Y.mj.eW i y = v i y)
    (i : Fin D.R.m) (σ k P α Rr) (hd : HkDat R Sb i k P α Rr) (hg : D.nd.goodRow σ) (y) (hy : y ∈ D.what₂.isot (i.1 + 1) σ) :
    hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e (v i y)) =
      D.what₂.embLL ((eig (i.1 + 1) σ k P : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e (v i y) := by
  rw [← H]
  exact h i σ k P α Rr hd hg y hy

end Gen

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} {N : TwNew (Dof x)}

abbrev RdTw (x : St P) (N : TwNew (Dof x)) : Type 1 :=
  R3.Read (datTw x N).R.toRealDat (datTw x N).F.lv2 (sideTw x N).p0

def jMtB (Y : RdTw x N) (μ h i y) : type_of% (x.r.Y.IL.jMt μ h i y).1 := (by with_unfolding_all exact ((Y.IL.jMt ((μ)) ((h)) ((i)) ((y))).1 : _))

def mtAd (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) {M : MtFam (Dof x)} (a : MtAd x.r.Y M) :
    MtAd Y (N.mt M) where
  PV i := ⟨(by with_unfolding_all exact ((a.PV ((i))).ψ : _)), (by with_unfolding_all exact ((a.PV ((i))).inj : _)), (by with_unfolding_all exact ((a.PV ((i))).into : _)), (by with_unfolding_all exact ((a.PV ((i))).onto : _))⟩
  std := (by with_unfolding_all exact (a.std :))
  eW := (by with_unfolding_all exact (a.eW :))
  read μ h i y g := (by with_unfolding_all exact (((a.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))).trans
    (congrFun (H ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) ((by with_unfolding_all exact (((a.PV ((i))).ψ ((g))) : _))))) :))
  rat := (by with_unfolding_all exact (a.rat :))
  wt := (by with_unfolding_all exact (a.wt :))
  id := (by with_unfolding_all exact (a.id :))

def eWB (Y : RdTw x N) (i y) : type_of% (x.r.Y.mj.eW i y) := (by with_unfolding_all exact ((Y.mj.eW ((i)) ((y))) : _))

theorem hkDat {Sb i k Q α Rr} (h : HkDat (datTw x N).R Sb i k Q α Rr) :
    HkDat x.m.z.R ((Sb)) ((i)) k ((Q)) ((α)) ((Rr)) :=
  ⟨(by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.offS :)), (by with_unfolding_all exact (h.odd :)), (by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.elt :)), (by with_unfolding_all exact (h.reps :))⟩

theorem eigAd (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) {Sb eig} (h : EigAd x.r.Y Sb eig) :
    EigAd Y ((Sb)) ((eig)) := fun i σ k Q α Rr hd hg y hy =>
  (by with_unfolding_all exact ((eigAd_of h (((eWB Y))) ((H)) ((i)) ((σ)) k ((Q)) ((α)) ((Rr)) (((hkDat hd))) ((hg)) ((y)) ((hy))) : _))

def inRat (Y : RdTw x N) (H : ∀ i y, x.r.Y.mj.eW i y = eWB Y i y) (n : InRat x.r.Y x.m.z.cG) : InRat Y (datTw x N).cG where
  kKs := (by with_unfolding_all exact (n.kKs :))
  hk := (by with_unfolding_all exact (n.hk :))
  In := (by with_unfolding_all exact ((ratIn N n.In) :))
  rat :=
    { hecke := fun j k Q α Rr h1 h2 hd y => (by with_unfolding_all exact ((n.rat.hecke j k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (α :))) ((by with_unfolding_all exact (Rr :))) h1 ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact ((hkDat hd) :))) ((by with_unfolding_all exact (y :)))) :))
      eig := (by with_unfolding_all exact ((eigAd Y H n.rat.eig) :))
      Sb_le := (by with_unfolding_all exact (n.rat.Sb_le :))
      lvl := (by with_unfolding_all exact (n.rat.lvl :))
      psi := (by with_unfolding_all exact (n.rat.psi :)) }

def li {hL : GlobalTheory.Published.LocalLanglandsGL} (l : LI hL x) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) (e : HEq (repOf r.Y) (repOf x.r.Y)) (mt : InMt r.Y (cfOf (stTw x N m hc hh r hp)) w.I.xi (QOf P)) (rat : InRat r.Y m.z.cG) :
    LI hL (stTw x N m hc hh r hp) where
  a := (by with_unfolding_all exact ((stA N l.a ((by with_unfolding_all exact ((repOf r.Y) :))) ((by with_unfolding_all exact (e :)))) :))
  Pq := (by with_unfolding_all exact (l.Pq :))
  Pq_over := (by with_unfolding_all exact (l.Pq_over :))
  sel := (by with_unfolding_all exact (l.sel :))
  mt := (by with_unfolding_all exact (mt :))
  rat := (by with_unfolding_all exact (rat :))
  cusp := (by with_unfolding_all exact ((cusp N l.cusp) :))

def inMt (Y : RdTw x N) (H : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB Y μ h i y) (n : InMt x.r.Y (cfOf x) w.I.xi (QOf P)) :
    InMt Y ((N.cf (cfOf x))) w.I.xi (QOf P) where
  M := (by with_unfolding_all exact ((N.mt n.M) :))
  ad := (by with_unfolding_all exact ((mtAd Y H n.ad) :))
  mt := (by with_unfolding_all exact ((mtIn N n.mt) :))

theorem li_copy : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : LI hL x) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hm : m.z = datTw x N) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N)) (hp : r.Pin), HEq (repOf r.Y) (repOf x.r.Y) → (∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (x.r.Y.IL.jMt μ h i y).1) → (∀ i y, HEq (r.Y.mj.eW i y) (x.r.Y.mj.eW i y)) → ∃ l' : LI hL (stTw x N m hc hh r hp), HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  intro hL K B f T w P x l N m hm hc hh r hp e H1 H2
  cases m
  dsimp only at hm
  subst hm
  have G1 : ∀ μ h i y, (x.r.Y.IL.jMt μ h i y).1 = jMtB (N := N) ((by with_unfolding_all exact (r.Y :))) μ h i y := fun μ h i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H1 ((μ)) ((h)) ((i)) ((y)))) : _)))
  have G2 : ∀ i y, x.r.Y.mj.eW i y = eWB (N := N) ((by with_unfolding_all exact (r.Y :))) i y := fun i y =>
    eq_of_heq ((by with_unfolding_all exact ((HEq.symm (H2 ((i)) ((y)))) : _)))
  refine Exists.intro (li l _ hc hh r hp e ((by with_unfolding_all exact ((inMt (N := N) ((r.Y)) ((G1)) l.mt) : _))) ((by with_unfolding_all exact ((inRat (N := N) ((r.Y)) ((G2)) l.rat) : _)))) ?_
  exact (by with_unfolding_all exact ((And.intro (HEq.refl (N.row l.a.A.row)) (And.intro (HEq.refl l.Pq) (And.intro (HEq.refl (N.rat l.rat.S))
    (And.intro (HEq.refl l.rat.In.Sb) (And.intro (HEq.refl l.rat.In.hL) (And.intro (HEq.refl l.rat.In.eig) (HEq.refl l.rat.In.θ))))))) :))

end GlobalTheory.HeightCounting.Up.LiTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideReadCell
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ValDelta

theorem exists_gal {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) (χ : HChar E) {n : ℕ} (hn : 0 < n) (hχ : χ.OrderDvd n) :
    ∃ r : G E Ω →* ℂˣ, Continuous r ∧ GlobalTheory.GalToHecke.IsHeckeOf art r χ := by
  have h1 : ∀ x, χ.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar E => ξ.1 x) hχ
  have hko : IsOpen (χ.1.ker : Set (Ideles E)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1
  have hkc : IsClosed (χ.1.ker : Set (Ideles E)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ χ.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact χ.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing E)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective
  let c : Gab E Ω →* ℂˣ := (QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, c (art x) = χ.1 x := fun x => by
    show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous c := by
    rw [ha.quot.isQuotientMap.continuous_iff]
    have : (c ∘ art) = χ.1 := funext hc
    rw [this]; exact χ.2.1
  refine ⟨c.comp (GlobalTheory.HeckeGal.toAb E Ω), hcc.comp continuous_quot_mk, fun x σ hσ => ?_⟩
  show χ.1 x = c (GlobalTheory.HeckeGal.toAb E Ω σ)
  rw [← hσ, hc]

variable {D : D7}

theorem delta_tame (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∈ D.ntw.pD i) : ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A, D.ntw.delta i σ ^ 15 = 1 := by
  refine ⟨fun h => ?_, fun A hA σ hσ => ?_⟩
  · have h1 := D.ntw.delta_tame i P hP
    have h2 : Ideal.absNorm P.asIdeal ∣ 15 ^ Module.finrank ℤ (𝓞 D.host.E) := by
      have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
      rwa [Ideal.absNorm_span_natCast] at this
    have h3 : Nat.Coprime (Ideal.absNorm P.asIdeal) 15 := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1]
      rfl
    have h4 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right _ h3) h2
    exact P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h4)
  · have h1 := pow_card_eq_one' (x := (⟨D.ntw.delta i σ, σ, hσ, rfl⟩ : (Ine (F := D.host.E) A).map (D.ntw.delta i)))
    rw [D.ntw.delta_15 i P hP A hA] at h1
    exact congrArg Subtype.val h1

theorem read_of_side {i : D.ntw.Tw} {b : Bool} {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) (y : D.ntw.O0 i)
    (x : ↥D.LL0) (h : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = (if b then D.ntw.emb0 i else D.ntw.emb0b i) x) :
    e (NX.ofO0 D i k y) = embLL0 D x := by
  rw [← he x, GlobalTheory.SeriesTie.sideEmb, RingHom.comp_apply, ← h]
  simp only [NX.toKk, IsFractionRing.map, IsLocalization.map_eq]
  rfl

theorem delta_isHeckeOf (cf : CharFrame D) (hR : DeltaRead D cf) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
    (ha : IsGlobalArtin art) {i : D.ntw.Tw} {b : Bool} {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) :
    GlobalTheory.GalToHecke.IsHeckeOf art ((Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp
      (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) (cf.delAt (D.ntw.l i)) := by
  obtain ⟨n, hn, hord⟩ : ∃ n, 0 < n ∧ (cf.delAt (D.ntw.l i)).OrderDvd n := by
    unfold CharFrame.delAt; split_ifs
    exacts [cf.isDel'.fin, cf.isDel.fin]
  obtain ⟨r, hr, hH⟩ := exists_gal ha _ hn hord
  have hker : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have hc : Continuous ((Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))) := by
    refine GlobalTheory.HeckeGal.continuous_of_isOpen_ker' _ (Subgroup.isOpen_mono (fun g hg => ?_) hker)
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]
  have hz : ∀ v, ‖(((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)‖ = 1 := fun v => cf.delAt_unitary _ _
  suffices h : (Units.map (e.comp (NX.ofO0 D i k)).toMonoidHom).comp (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) = r by
    rw [h]; exact hH
  refine GlobalTheory.GalChar.eq_of_frob ha hc hr ?_
  filter_upwards [GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero,
    GlobalTheory.GalChar.unr_ae (cf.delAt (D.ntw.l i))] with v hv hu A hA σ hσ
  obtain ⟨x, hx, hd⟩ := hR i v hv hu A σ hA hσ
  have hx' : D.what₂.embLL (x : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val v : ℂˣ) : ℂ)⁻¹ := by
    rw [hx, Units.val_inv_eq_inv_val]
  have hrv : r σ = ((cf.delAt (D.ntw.l i)).val v)⁻¹ := by rw [hH.val_eq ha hu hA hσ, inv_inv]
  rw [hrv]
  cases b
  · have hstar : (x : D.what₂.LL) = star ((x⁻¹ : D.LL0) : D.what₂.LL) := by
      apply D.what₂.embLL.injective
      rw [D.starLL_cx, IntermediateField.coe_inv, map_inv₀, hx', inv_inv, ← Complex.inv_eq_conj (hz v)]
    have h1 := read_of_side he _ x⁻¹ (hd.trans (D.ntw.restX_coefficientEmbedding_conj i x⁻¹ x hstar).symm)
    show Units.map _ ((D.ntw.delta i σ)⁻¹) = _
    rw [map_inv, inv_inj]
    apply Units.ext
    refine h1.trans ?_
    show D.what₂.embLL ((x⁻¹ : D.LL0) : D.what₂.LL) = _
    rw [IntermediateField.coe_inv, map_inv₀, hx', inv_inv]
  · apply Units.ext
    exact (read_of_side he _ x hd).trans hx

theorem tameVal_delta (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (cf : CharFrame D) (hR : DeltaRead D cf) {i : D.ntw.Tw} {b : Bool}
    {k : ℕ} {e : NX.Kk D i k →+* ℂ} (he : SideRead i b k e) {P : PlE D.host} (hP : P ∈ D.ntw.pD i) (a : 𝓞 D.host.E)
    (y : D.host.Eˣ) (hu : a ∉ P.asIdeal) (hy : (y : D.host.E) = (a : D.host.E)) :
    IsUnitAt P (atFin P y) ∧ e (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then 1 else -1) a).1) =
      (((cf.delAt (D.ntw.l i)).locK P y : ℂˣ) : ℂ) := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  have hA : IsPlaceOver (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  obtain ⟨hq2, hq1⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ0 : 𝓞 D.host.E, ϖ0 ∈ P.asIdeal ∧ ϖ0 ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E))
    (show 0 < normV P - 1 by omega)
  have hxu : IsUnitAt P (atFin P y) := by
    show Valued.v (((y : D.host.E) : P.adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  refine ⟨hxu, ?_⟩
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    P _ hA ϖ hϖ1 hϖ2 π hπ (atFin P y) a hxu (by simp [atFin, hy])
  obtain ⟨h15, hord⟩ := delta_tame i hP
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep (D.ntw.delta i) P _ 15 (D.ntw.delta_open i) h15
    (fun A hA σ hσ => ⟨1, by rw [pow_one, hord A hA σ hσ]⟩) _ a hu
    (GlobalTheory.TameResRead.tameRep_zpow hA hσI hϖ1 hϖ2 hπ hu hσval _)]
  have h1 := delta_isHeckeOf cf hR ha he _ σ hσart.symm
  have h2 : D.ntw.delta i (σ ^ (if b then (1 : ℤ) else -1)) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ := by
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  rw [h2]
  exact (congrArg Units.val h1).symm

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofO0 (Dof x) i (T.k v) (NX.tameVal ((Dof x).ntw.delta i) P' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  intro hP hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok e he _ P' hP' a k ha hk
  have h2 := P.q.mu.tw v
  have hp : P' ∈ (Dof x).ntw.pD i := (cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP'
  obtain ⟨hxu, hv⟩ := tameVal_delta hP.what₂.art (cfOf x) l.b.Bs.deltaRead he hp a k ha hk
  rw [l.b.Bs.exp.sgnT_one]
  refine hv.trans (congrArg Units.val ?_)
  have hp' : P' ∈ placesOver (Dof x).host.E (if (Dof x).ntw.l i = (Dof x).host.pde then (Dof x).host.pde' else (Dof x).host.pde) := by
    rw [← (Dof x).ntw.pD_eq i]; exact hp
  obtain ⟨h1, -, h3, -, -⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe (cfOf x)) (l := (Dof x).ntw.l i)
  have hmu : ((cfOf x).mu0 j).UnrAt P' :=
    ((cfOf x).isMu0 j).unr P' fun kk => GlobalTheory.GalChar.notMem_of_ne h1 ((Dof x).host.g_prime kk) (h3 kk) hp'
  have hψ : (T.psi v).UnrAt P' := by
    change P' ∈ placesOver B.host.E (if (Dof x).ntw.l i = B.host.pde then B.host.pde' else B.host.pde) at hp'
    split_ifs at hp'
    · exact BadV.unr_of_twist (T.psi_tw v) B.host.pde'_prime (by simp [offSet]) P' hp'
    · exact BadV.unr_of_twist (T.psi_tw v) B.host.pde_prime (by simp [offSet]) P' hp'
  have hdel : (cfOf x).delAt ((Dof x).ntw.l i) = if B.places.resChar v = B.host.pde then f.del' else f.del := by
    rw [hl]
    exact congrArg (fun c : Top.Fr B.toPre => if B.places.resChar v = B.host.pde then c.del' else c.del) w.C_eq
  have key : ∀ (u : HeightOneSpectrum (𝓞 B.host.E)) (μ δ ξ : HChar B.host.E) (y), IsUnitAt u y → μ.UnrAt u → ξ.UnrAt u →
      δ.loc u y = (μ * (δ * ξ)).loc u y := by
    intro u μ δ ξ y hy h1 h2
    rw [HChar.loc_mul, HChar.loc_mul, h1 _ hy, h2 _ hy, one_mul, mul_one]
  rw [hdel]
  exact (key P' _ _ _ _ hxu hmu hψ).trans
    (congrArg (fun ξ : HChar B.host.E => (@HMul.hMul (HChar B.host.E) (HChar B.host.E) _ _ ((cfOf x).mu0 j) ξ).loc P' (atFin P' k)) h2.symm)

end GlobalTheory.LevCmp.ValDelta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideReadStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reads_hecke_of_side_read : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofOk (Dof x) i (T.k v) (NX.tameVal ψ P' l.b.Bs.exp.sgnT a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.LevCmp.ValQ.main | exact GlobalTheory.LevCmp.ValQ.main | (intros; apply GlobalTheory.LevCmp.ValQ.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleRationalFormLiftsAlgebraicEnlarged
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.RatExt

open Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Mem.R3.Rw.LiftExt

private theorem comb_gen {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E'] (Y : HMod E) (X : HMod E')
    (g : Y.H →ₗ[ℂ] X.H) (hinj : Function.Injective Y.e) (v : Y.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g v := by
  have e : v = ∑ k, s k • u k := hinj (by rw [eq_of_heq hv, map_sum]; simp only [map_smul])
  rw [e, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, eq_of_heq (hp k)]

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {V W : HSp a.D} {V' W' : HSp a'.D} {S : a.D.what₂.Tau → SPar} {S' : a'.D.what₂.Tau → SPar} {M : DSModel W S} {M' : DSModel W' S'}

private theorem comb_of (hP : B'.toPre = B.toPre) (hV : HEq V' V) (hW : HEq W' W) (h : DSTie M' M) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW)
    {Y : HMod (Bridge.Gf V → c.W)} {Y' : HMod (Bridge.Gf V' → c'.W)} (hY : HEq Y' Y)
    {X : HMod (MMap M)} {X' : HMod (MMap M')} (hX : HEq X' X) {g : Y.H →ₗ[ℂ] X.H} {g' : Y'.H →ₗ[ℂ] X'.H} (hg : HEq g' g)
    (hinj : Function.Injective Y.e) (v : Y'.H) {n : ℕ} (s : Fin n → ℂ) (u : Fin n → Y.H)
    (hv : HEq (Y'.e v) (∑ k, s k • Y.e (u k))) (p : Fin n → X'.H) (hp : ∀ k, HEq (p k) (g (u k))) : ∑ k, s k • p k = g' v := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (W')) ((by with_unfolding_all exact ((W) :))) (W') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W')) (W') (((W))) (((hW)))).symm : _))
  clear (hW)
  subst e))
  obtain ⟨H', s', l', ε', f', _, _, _, _⟩ := M'
  rename_i n' i' _ _ _ _
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  dsimp only at h1 h2 h3 h4 h5 h6 h7
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((M.H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((M.H))) (((h1)))).symm : _))
  clear (h1)
  subst e))
  ( (
  have e : @Eq (type_of% (n')) ((by with_unfolding_all exact ((M.nacg) :))) (n') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (n')) (n') (((M.nacg))) (((h2)))).symm : _))
  clear (h2)
  subst e))
  ( (
  have e : @Eq (type_of% (i')) ((by with_unfolding_all exact ((M.ips) :))) (i') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (i')) (i') (((M.ips))) (((h3)))).symm : _))
  clear (h3)
  subst e))
  ( (
  have e : @Eq (type_of% (s')) ((by with_unfolding_all exact ((M.σ) :))) (s') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (s')) (s') (((M.σ))) (((h4)))).symm : _))
  clear (h4)
  subst e))
  ( (
  have e : @Eq (type_of% (l')) ((by with_unfolding_all exact ((M.lam) :))) (l') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (l')) (l') (((M.lam))) (((h5)))).symm : _))
  clear (h5)
  subst e))
  ( (
  have e : @Eq (type_of% (ε')) ((by with_unfolding_all exact ((M.ε) :))) (ε') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ε')) (ε') (((M.ε))) (((h6)))).symm : _))
  clear (h6)
  subst e))
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((M.fr) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((M.fr))) (((h7)))).symm : _))
  clear (h7)
  subst e))
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ( (
  have e : @Eq (type_of% (W₁)) ((by with_unfolding_all exact ((c.W) :))) (W₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W₁)) (W₁) (((c.W))) (((c1)))).symm : _))
  clear (c1)
  subst e))
  ( (
  have e : @Eq (type_of% (nW')) ((by with_unfolding_all exact ((c.nW) :))) (nW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nW')) (nW') (((c.nW))) (((c3)))).symm : _))
  clear (c3)
  subst e))
  ( (
  have e : @Eq (type_of% (iW')) ((by with_unfolding_all exact ((c.iW) :))) (iW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (iW')) (iW') (((c.iW))) (((c4)))).symm : _))
  clear (c4)
  subst e))
  ( (
  have e : @Eq (type_of% (ρ₁)) ((by with_unfolding_all exact ((c.ρ) :))) (ρ₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ρ₁)) (ρ₁) (((c.ρ))) (((c2)))).symm : _))
  clear (c2)
  subst e))
  ( (
  have e : @Eq (type_of% (Y')) ((by with_unfolding_all exact ((Y) :))) (Y') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Y')) (Y') (((Y))) (((hY)))).symm : _))
  clear (hY)
  subst e))
  ( (
  have e : @Eq (type_of% (X')) ((by with_unfolding_all exact ((X) :))) (X') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (X')) (X') (((X))) (((hX)))).symm : _))
  clear (hX)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  exact (by with_unfolding_all exact ((comb_gen Y X g hinj ((v)) s u ((hv)) ((p)) ((hp))) : _))

end Comparison₂

private theorem apply_eq {m m' : ℕ} (hm : m' = m) {F : Fin m → ℕ} {F' : Fin m' → ℕ} (hF : HEq F' F) {i : Fin m} {i' : Fin m'}
    (h : (i : ℕ) = i') : F i = F' i' := by
  subst hm
  obtain rfl := eq_of_heq hF
  obtain rfl : i = i' := Fin.ext h
  rfl

section Fields

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}

set_option maxHeartbeats 1000000 in

private theorem rat_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW)
    (hM : DSTie (R'.MW i' a'.D.what₂.embLL) (R.MW i a.D.what₂.embLL)) (hHW : HEq (R'.HW i' a'.D.what₂.embLL) (R.HW i a.D.what₂.embLL))
    (hHV : HEq (R'.HV i' t') (R.HV i t)) (hg : HEq (R'.thG i' t') (R.thG i t)) (hn : HEq R'.nW R.nW)
    (ι : a.D.what₂.LL →+* a'.D.what₂.LL) (hι : ∀ x, a'.D.what₂.embLL (ι x) = a.D.what₂.embLL x)
    (hj : ∀ (σ' : a'.D.what₂.LL →+* ℂ) x x', CrdOver ι x x' → HEq ((R'.FW i').j σ' x') ((R.FW i).j (σ'.comp ι) x))
    (hinj : Function.Injective (R.HV i t).e) (hjV : ∀ x, (R.HV i t).e (R.jV i t x) = R.B.jL i t x) (hr : RatAt R t)
    (x' : A'.fam.amb.FL i' t') {n : ℕ} (b : Fin n → a'.D.what₂.LL) (x : Fin n → A.fam.amb.FL i t)
    (hx : HEq (R'.B.jL i' t' x') (∑ k, a'.D.what₂.embLL (b k) • R.B.jL i t (x k)))
    (v : (R'.HV i' t').H) (hv : (R'.HV i' t').e v = R'.B.jL i' t' x') :
    ∃ y, (R'.FW i').j (sg0 a'.D A') y = R'.thG i' t' v := by
  have s : a.D.what₂.embLL = sg0 a.D A := (sgAt_mk _ R.hv0).symm
  have s' : a'.D.what₂.embLL = sg0 a'.D A' := (sgAt_mk _ R'.hv0).symm
  have hM0 : DSTie (R'.MW i' (sg0 a'.D A')) (R.MW i (sg0 a.D A)) := s ▸ s' ▸ hM
  have hHW0 : HEq (R'.HW i' (sg0 a'.D A')) (R.HW i (sg0 a.D A)) := s ▸ s' ▸ hHW
  have hc : (sg0 a'.D A').comp ι = sg0 a.D A := by
    rw [← s, ← s']; exact RingHom.ext hι
  have hmv : ∀ (σ₁ σ₂ : a.D.what₂.LL →+* ℂ), σ₁ = σ₂ → ∀ y, HEq ((R.FW i).j σ₁ y) ((R.FW i).j σ₂ y) := by
    intro σ₁ σ₂ e y; subst e; exact HEq.rfl
  have hn0 : R.nW i = R'.nW i' := apply_eq (LiftExt.m_eq hP) hn h
  choose y hy using fun k => hr i (x k) (R.jV i t (x k)) (hjV (x k))
  refine ⟨∑ k, b k • GeoFW.crdMap ι hn0 (y k), ?_⟩
  refine ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => LinearMap.map_smulₛₗ _ _ _)).trans ?_
  refine comb_of hP (vc_heq hP h) (wc_heq hP h) hM0 c1 c2 c3 c4 hHV hHW0 hg hinj v (fun k => sg0 a'.D A' (b k))
    (fun k => R.jV i t (x k)) ?_ (fun k => (R'.FW i').j (sg0 a'.D A') (GeoFW.crdMap ι hn0 (y k))) fun k => ?_
  · refine (heq_of_eq hv).trans (hx.trans (heq_of_eq ?_))
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (by with_unfolding_all exact ((congrArg₂ (fun (c : ℂ) (q : Bridge.Gf (Vc a.D i) → (R.cV i).W) => c • q) (DFunLike.congr_fun s' (b k)) (hjV (x k)).symm) :))
  · exact ((hj _ _ _ (GeoFW.crdOver_crdMap ι hn0 (y k))).trans (hmv _ _ hc _)).trans (heq_of_eq (hy k))

end Fields

end GlobalTheory.Mem.R3.Rw.RatExt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_rationalForm_lifts_algebraic_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSide z Wt' R' → JSpan z Wt' R' → RatAt z.R.toRealDat (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) → RatAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hS hJ hr i' x' v hv
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  obt ⟨⟨-, -, -, -, -, hn, -, -, -, -, -, -, h1, -⟩, h2⟩ := hS
  obt ⟨c1, c2, c3, c4, -, -, -, m1, m2, m3, m4, m5, m6, m7, -, hHW, -, -, hWι⟩ := h1 i i' h
  obt ⟨-, -, hHV, -, hg, -, -⟩ := h2 i i' h
  obt ⟨n, b, x, hx⟩ := hJ i i' h x'
  have hb := z.pins.char.base.models
  exact RatExt.rat_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h c1 c2 c3 c4
    ⟨m1, m2, m3, m4, m5, m6, m7⟩ hHW hHV hg hn ι hι (fun σ' => ((hWι ι hι).1 σ').2.2.2) (hb.HV i _).1 (hb.jV i _) hr x' b x hx v hv
end

