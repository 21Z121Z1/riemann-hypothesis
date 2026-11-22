import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCastMap
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

section Alg

theorem coef_agree {L K L' K' I W W' : Type} [Field L] [Field K] [Field L'] [Field K'] [Fintype I] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] {n : ℕ} (lam : I → DomWeight n) {σL : L →+* ℂ} {σK : K →+* ℂ} {σL' : L' →+* ℂ} {σK' : K' →+* ℂ}
    (jL : L →+* K) (jL' : L' →+* K') (inc : K →+* K') (h : σK.comp jL = σL) (h' : σK'.comp jL' = σL') (hi : σK'.comp inc = σK)
    (s : Function.Surjective jL) (s' : Function.Surjective jL')
    {cL : VV L lam →ₛₗ[σL] W} {cK : VV K lam →ₛₗ[σK] W} {cL' : VV L' lam →ₛₗ[σL'] W'} {cK' : VV K' lam →ₛₗ[σK'] W'}
    (hc : ∀ v : VV L lam, ∃ v' : VV K lam, (v' : Pol K I n) = MvPolynomial.map jL (v : Pol L I n) ∧ cK v' = cL v)
    (hc' : ∀ v : VV L' lam, ∃ v' : VV K' lam, (v' : Pol K' I n) = MvPolynomial.map jL' (v : Pol L' I n) ∧ cK' v' = cL' v)
    (ha : ∀ (v : VV L lam) (v' : VV L' lam), HEq (MvPolynomial.map σL' v'.1) (MvPolynomial.map σL v.1) → HEq (cL' v') (cL v))
    (v : VV K lam) (v' : VV K' lam) (e : (v' : Pol K' I n) = MvPolynomial.map inc (v : Pol K I n)) : HEq (cK' v') (cK v) := by
  have key : ∀ {L K : Type} [Field L] [Field K] (jL : L →+* K), Function.Surjective jL → ∀ v : VV K lam,
      ∃ u : VV L lam, (v : Pol K I n) = MvPolynomial.map jL (u : Pol L I n) := by
    intro L K _ _ jL s v
    let q := (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).symm
    refine ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV q.toRingHom lam _ v.2⟩, ?_⟩
    have : jL.comp q.toRingHom = RingHom.id K := RingHom.ext fun x => (RingEquiv.ofBijective jL ⟨jL.injective, s⟩).apply_symm_apply x
    rw [MvPolynomial.map_map, this, MvPolynomial.map_id]
  obtain ⟨u, hu⟩ := key jL s v
  obtain ⟨u', hu'⟩ := key jL' s' v'
  obtain ⟨a, a1, a2⟩ := hc u
  obtain ⟨b, b1, b2⟩ := hc' u'
  obtain rfl : a = v := Subtype.ext (a1.trans hu.symm)
  obtain rfl : b = v' := Subtype.ext (b1.trans hu'.symm)
  rw [a2, b2]
  refine ha u u' (heq_of_eq ?_)
  rw [← h, ← h', ← MvPolynomial.map_map, ← MvPolynomial.map_map, ← hu, ← hu', e, MvPolynomial.map_map, hi]

theorem exists_cast_map {K V W W' : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}
    (n : NormedAddCommGroup W) (p : InnerProductSpace ℂ W) (n' : NormedAddCommGroup W') (p' : InnerProductSpace ℂ W')
    (hW : HEq W' W) (hn : HEq n' n) (hp : HEq p' p) (c' : V →ₛₗ[σ] W') :
    ∃ c : V →ₛₗ[σ] W, HEq c' c ∧ ∀ v, HEq (c' v) (c v) := by
  cases hW; cases hn; cases hp
  exact ⟨c', HEq.rfl, fun _ => HEq.rfl⟩

end Alg

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Change

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) (c₃ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hs : O.c'.F ≤ c₃.F)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (h : O.Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

abbrev bc : OMDat C R i Unit (fun _ => A.μ0) :=
  merge (tup := fun _ : Unit => A.μ0) (fun _ => O) c₃ (O.hle.trans hs) (fun _ => hs) ((incF O.c' c₃ hs).comp O.jL) O.hV c0₃ O.lev
    io₃ hw₃ (fun _ => 1) (fun _ => h) v₀

structure IsBC (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (J' : Subgroup (Bridge.Gf (Vc D i))) : Prop where
  c0 : ∀ (v : VsV D i O.c'.F) (v' : VsV D i c₃.F), (v' : Pol c₃.F D.what₂.Tau (Vc D i).rank) =
    MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F D.what₂.Tau (Vc D i).rank) → c0₃ v' = O.c0' v
  io : IoOver hs (lamV D i) O.io io₃
  reps : RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ())
  placeEx : PlaceEx R i A.μ0 h O.c0'
  thAd : ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ())
  plc : ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x
  pins : (bc O c₃ hs c0₃ io₃ hw₃ h v₀).Pins κ v₀ ι x₀

set_option maxHeartbeats 1600000 in

theorem exists_isBC (hV : R.models_HV) {κ ι x₀} (hO : O.Pins κ v₀ ι x₀)
    (hc0 : ∀ (v : VsV D i O.c'.F) (v' : VsV D i c₃.F), (v' : Pol c₃.F D.what₂.Tau (Vc D i).rank) =
      MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F D.what₂.Tau (Vc D i).rank) → c0₃ v' = O.c0' v) :
    ∃ io₃ hw₃ h J', IsBC O c₃ hs c0₃ io₃ hw₃ h v₀ κ ι x₀ J' := by
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.IoExtend.exists_ioLFRec_over _ _ _ _ O.c' c₃ hs _ _ (tauE D) (lamV D i) (wtA κ) O.io O.hw hO.io
  obtain ⟨h, J', hr, hpl, hth, hplc⟩ := (hO.tuple ()).reps
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  refine ⟨io₃, hw₃, h, J', hc0, hover, hr, hpl, hth, hplc, ⟨?_, hO.lift.std, hO.lift.v0, ?_, hO.lift.lev⟩,
    fun j => ⟨?_, (hO.tuple ()).B, (hO.tuple ()).xi, (hO.tuple ()).phi, (hO.tuple ()).half⟩,
    ⟨hO.act.1, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ (O.hle.trans hs) _ _ hO.act.1).1⟩, fun j => hO.bad (), fun j => hO.reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ hs) ((hO.ep ()).1 k), epIs_map hs (hO.ep ()).2⟩, hio,
    fun j k q => phiHat_covBC hs _ 1 _ _ q (hO.w () k q),
    fun j => covPin_covBC hs _ one_ne_zero (hO.cov ()), ?_, fun j => hO.model₂ ()⟩
  · exact (RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field
  · obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV (incF O.c' c₃ hs) _ _ v'.2⟩, (congrArg (MvPolynomial.map (incF O.c' c₃ hs)) hv').trans (MvPolynomial.map_map _ _ _),
      (hc0 v' _ rfl).trans e⟩
  · refine ⟨h, J', repsR_map _ hr, fun x₀ => ?_, thAdIs_thAdOf R i A.μ0 h c0₃ hV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
    obtain ⟨x, hx⟩ := hpl x₀
    exact ⟨fun k => ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV (incF O.c' c₃ hs) _ _ (x k).2⟩, fun k => (hx k).trans (hc0 _ _ rfl).symm⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨a, ha, fun j => ?_⟩
    have key := GlobalTheory.OneMapAll.cXiAt_covBC D _ _ _ _ _ _ _ _ hs _ _ _ 1 _ _ _ _ _ _ (hO.cov ()).1.2.2.2.2.2.2.2.1 (hca ())
    exact (congrArg (GlobalTheory.OneMapAll.CXiAt _ _ _ _ _ _ _ _ _) (one_mul a)).mp key

end Change

section Tuple

open Classical in
variable (D) in

def TupOver (i : Fin D.R.m) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (βV : ∀ i, GL (Fin (Vc D i).rank) (Lev.EAf D))
    (βW : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)) (χ : Formalism.L2.Host.HChar D.host.E) (ξ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) {K' : Type} [Field K'] (σ' : K' →+* ℂ)
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (bad : ℕ) (Mb I : Ideal (𝓞 D.host.E)) (N : Submodule (𝓞 D.host.E) La) {Cl : Type} (h : Cl → GA D (Vc D i))
    (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K')
    (B : Ideal (𝓞 D.host.E) → K') (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (φ : (Fin (Vc D i).rank → La ⧸ N) → K') : Prop :=
  (bad ≠ 0 ∧ (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    J' ≤ (levEnv (Vc D i) (βV i) (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ∧
    J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J ≠ 0 ∧
    vol = ((J'.relIndex (levEnv (Vc D i) (βV i)
      (datY _ D.R.r D.R.t 1 (r_le_V i) Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.A)).J : ℕ) : K')⁻¹ ∧
    Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => fin _ (h k)) ∧
    ∀ k, SplitOffBad (Vc D i) bad (h k) ∧ Lh k = Bridge.hLat (Vc D i) (fin _ (h k)) ∧
      gam k = Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin _ (h k)))) ∧
  (∀ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ → cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ →
    σ' (B cc) = ((χ.onId (cc : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ)) ∧
  (∀ (g : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) g x →
    ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)) ∧
  (∃ e : AE D, IsIdemSum e (Pg ∪ Q) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b)) ∧
    σ' (φ fun b => Submodule.Quotient.mk (x b)) =
      omegaK Pg (fun PP => redM PP (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b))) *
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (uMat (Vc D i) (Wc D i) (βV i) (βW i) e fun b => ι (x b)))) ∧
  (Mb = ∏ PP ∈ Pg, PP.asIdeal ∧ (∀ PP ∈ Q, I ≤ PP.asIdeal) ∧
    ∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)

variable {i : Fin D.R.m} {K' : Type} [Field K'] {σ' : K' →+* ℂ}
  {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {bad : ℕ} {Mb I : Ideal (𝓞 D.host.E)} {N : Submodule (𝓞 D.host.E) La} {Cl : Type} {h : Cl → GA D (Vc D i)}
  {J' : Subgroup (Bridge.Gf (Vc D i))} {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
  {B : Ideal (𝓞 D.host.E) → K'} {xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} {φ : (Fin (Vc D i).rank → La ⧸ N) → K'}

set_option maxHeartbeats 1000000 in

theorem tupOver_iff {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T0) :
    TupOver D i R.Pg (R.Q t) R.βV R.βW (R.C.mu0 i * R.xiH t * R.C.eta⁻¹) (R.xi t) (R.xiR t) σ' ι bad Mb I N h J' Lh gam vol B xi φ ↔
      RepsR R i t h bad J' Lh gam vol ∧ BIs R i σ' t bad B ∧ XiIs R i t xi ∧ PhiIs R i σ' t ι N φ ∧ HalfIs R t Mb I := Iff.rfl

theorem tupOver_cast {Pg₁ Pg₂ Q₁ Q₂ : Finset (Formalism.L2.DIV.Pl D.host.E)} {βV₁ βV₂ βW₁ βW₂ χ₁ χ₂ ξ₁ ξ₂ ξR₁ ξR₂}
    (hP : HEq Pg₂ Pg₁) (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅) (hV : HEq βV₂ βV₁) (hW : HEq βW₂ βW₁) (hχ : χ₂ = χ₁) (hξ : ξ₂ = ξ₁)
    (H : TupOver D i Pg₁ Q₁ βV₁ βW₁ χ₁ ξ₁ ξR₁ σ' ι bad Mb I N h J' Lh gam vol B xi φ) :
    TupOver D i Pg₂ Q₂ βV₂ βW₂ χ₂ ξ₂ ξR₂ σ' ι bad Mb I N h J' Lh gam vol B xi φ := by
  cases hP; cases hV; cases hW
  subst hQ₁ hQ₂ hχ hξ
  obtain ⟨h1, h2, h3, ⟨e, he, h4⟩, h5⟩ := H
  refine ⟨h1, h2, h3, ⟨e, he, fun x => ⟨(h4 x).1, (h4 x).2.trans ?_⟩⟩, h5⟩
  simp [omegaQ]

end Tuple

section Same

variable {D' : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0' T0' : Type} {A' : FamIn D'.what₂.LL G' Pl0' T0' D'.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  {C' : Core D'} [Algebra C'.Q.c.F D'.what₂.LL] {R' : RealDat D' A' C'.Q.c.F} {i' : Fin D'.R.m}

structure SameGeo (O' : OMDat C' R' i' Unit (fun _ => A'.μ0)) (M : OMDat C R i Unit (fun _ => A.μ0)) : Prop where
  c' : HEq O'.c' M.c'
  lev : HEq O'.lev M.lev
  dδ : HEq O'.dδ M.dδ
  Cl' : O'.Cl' = M.Cl'
  fCl : HEq O'.fCl M.fCl
  bad : O'.bad = M.bad
  Lh : HEq O'.Lh M.Lh
  La : HEq O'.La M.La
  Nc : HEq O'.Nc M.Nc
  gam : HEq O'.gam M.gam
  vol : HEq O'.vol M.vol
  ep : HEq O'.ep M.ep
  B : HEq O'.B M.B
  epF : HEq O'.epF M.epF
  io : HEq O'.io M.io
  hw : HEq O'.hw M.hw
  φ : HEq O'.φ M.φ
  w : HEq O'.w M.w
  U₂ : HEq O'.U₂ M.U₂
  dict₂ : HEq O'.dict₂ M.dict₂
  xi : HEq O'.xi M.xi

def IsBCOf (O' : OMDat C' R' i' Unit (fun _ => A'.μ0)) (v₀' : (R'.MW i' (sg0 D' A')).Vec) (O : OMDat C R i Unit (fun _ => A.μ0))
    (v₀ : (R.MW i (sg0 D A)).Vec) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (P : Prop) : Prop :=
  ∃ c₃ hs c0₃ io₃ hw₃ h J', IsBC O c₃ hs c0₃ io₃ hw₃ h v₀ κ ι x₀ J' ∧ SameGeo O' (bc O c₃ hs c0₃ io₃ hw₃ h v₀) ∧
    (HEq O'.c0' c0₃ ∨ P) ∧ ∃ (h' : O'.Cl' () → GA D' (Vc D' i')) (J'' : Subgroup (Bridge.Gf (Vc D' i'))), HEq h' h ∧ HEq J'' J' ∧
      RepsR R' i' A'.μ0 h' (O'.bad ()) J'' (O'.Lh ()) (O'.gam ()) (O'.vol ()) ∧ PlaceEx R' i' A'.μ0 h' O'.c0' ∧
      ThAdIs R' i' A'.μ0 h' O'.c0' v₀' (O'.thAd ()) ∧ ∀ x, O'.Plc () x ↔ ∃ x₀, Place R' i' A'.μ0 h' O'.c0' (jVx R' i' A'.μ0 x₀) x

theorem IsBCOf.lev {O' : OMDat C' R' i' Unit (fun _ => A'.μ0)} {v₀'} {O : OMDat C R i Unit (fun _ => A.μ0)} {v₀ κ ι x₀ P}
    (h : IsBCOf O' v₀' O v₀ κ ι x₀ P) : HEq O'.lev O.lev := by
  obtain ⟨_, _, _, _, _, _, _, -, hs, -⟩ := h
  exact hs.lev

end Same

theorem wtA_eq {j : ℕ} (κ κ' : WeightFamilies.Wt D j) (hP : κ'.aP = κ.aP) (hM : κ'.aM = κ.aM) : wtA κ' = wtA κ := by
  funext x
  simp only [wtA, hP, hM]

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacePenultimateChartCharacterInverseValu
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.LocVal

theorem midLev_one_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (al : (I.idx a).β i)
    (P : SBof I a) : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) 1 1 := by
  classical
  obtain ⟨z, r, hr, hrx, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) 1).2 (Subgroup.one_mem _)
  refine ⟨r, hr, hrx, ?_⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [chiInv_at_type I hOk a i al P hP 1 1 r hr hrx 1 (one_mem _) (fun x _ => by simp) (congE_refl _ _ _)]
    have e : (((I.idx a).levG i al) ⟨P.1, hP⟩).lam ⟨1, one_mem _⟩ = 1 := map_one (((I.idx a).levG i al) ⟨P.1, hP⟩).lam
    rw [e]; simp
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    rw [chiInv_at_twist I hOk a i hi al P hQ 1 1 r hr hrx 1 (one_mem _) (by simp) (congE_refl _ _ _)]
    have e : (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam ⟨1, one_mem _⟩ = 1 := map_one (((I.idx a).levQ i al) ⟨P.1, hQ⟩).lam
    rw [e]; simp

open Classical in

theorem exists_frNear_one_over {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n : ℕ)
    (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hk : bc (prV (E := (I.rec7 l Z).host.E) v) k = 1) :
    ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb ∧ ∀ P, IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → fb P = 1 := by
  obtain ⟨fb0, h0⟩ := GlobalTheory.Mem.Col2.AdT.frNear_exists I hOk l Z a n k
  refine ⟨fun P => if IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) then 1 else fb0 P, fun P => ?_, fun P hP => if_pos hP⟩
  by_cases hv : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
  · simp only [if_pos hv]
    refine ⟨?_, ?_⟩
    · have h2 := GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hv ((I.cst a).D P) k 1 (by rw [map_one, hk])
      simpa using h2
    · have h2 := GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hv ((I.cst a).D P) 1 k (by rw [map_one, hk])
      simpa using h2
  · simp only [if_neg hv]
    exact h0 P

theorem nearAt_emb_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hP : ¬ IsOver v P) (d : ℕ)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin n) E) (hg : g = 1) :
    GlobalTheory.TwU.NearAt P d (y⁻¹ * GlobalTheory.Mem.Col2.ChartLevel.emb v x * y) g := by
  subst hg
  have hw : IsOver (P.under (𝓞 F)) P := by
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  have hne : P.under (𝓞 F) ≠ v := fun e => hP (e ▸ hw)
  unfold GlobalTheory.TwU.NearAt
  refine GlobalTheory.AwayFr.congAt_of_prV_eq _ _ hw d _ _ ?_
  rw [map_one, map_one, map_mul, map_mul, GlobalTheory.Mem.Col2.ChartLevel.emb_ne hne, mul_one, ← map_mul, inv_mul_cancel, map_one]

end GlobalTheory.Mem.Col2.QChi.LocVal

namespace GlobalTheory.Mem.Col2.QChi

set_option maxHeartbeats 4000000 in

theorem chi_embU_mul_valV : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), (((K β).lev.chi (GlobalTheory.Mem.Col2.ChartLevel.embU (K β).lev v x) : ℂˣ) : ℂ) * GlobalTheory.Mem.Col2.QChi.valV I l Z a v x.1 = 1 := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ _ _ hRd hFin _ _ Lb0 _ v hvQ β x
  classical
  obtain ⟨k, hR, hk1⟩ := hRd
  obtain ⟨c, rfl⟩ := hR.onto β
  obtain ⟨fb, hfb, hfb1⟩ := LocVal.exists_frNear_one_over I hOk l Z a _ (k (chOf c)) v (hk1 _ v ((hQ v).1 hvQ))
  have hm : B.R.m - 1 < B.R.m := by omega
  have hlast : B.R.m - 1 + 1 = B.R.m := by omega
  let y0 : SBof I a → Sp B.fields.E (B.R.N (B.R.m - 1)) := fun P =>
    ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 hlast).1.some
  have H := lev_mid hOk hPins hR c hfb (hFin _) hm y0
    (Rel := fun P g z => MidAt I hm c.1 P g z ∧ (B.R.m - 1 + 1 = B.R.m → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P)))
    (fun _ P => ((GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime I hOk u a _ ((I.stp u a _).rep c) P).2 hlast).1.some_mem) (fun _ _ _ => Iff.rfl)
  have hx : bc (prV (E := (I.rec7 l Z).host.E) v) (GlobalTheory.Mem.Col2.ChartLevel.emb v x.1) ∈ (K (chOf c)).lev.Uloc v := by
    rw [GlobalTheory.Mem.Col2.ChartLevel.emb_self]; exact x.2
  have key : ∀ (P : SBof I a) (j : ℕ), j = B.R.m - 2 + 1 → ∀ b, (I.idx a).h j b P = 1 := by
    rintro P j rfl b
    exact (hOk.idx_ok a).last_h b P
  have hall : ∀ P : SBof I a, ∃ g z, ((MidAt I hm c.1 P g z ∧ (B.R.m - 1 + 1 = B.R.m →
      GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g (y0 P)) (y0 P))) ∧
      GlobalTheory.TwU.InFrame (sm I l Z) fb (I.cst a).D P (GlobalTheory.Mem.Col2.ChartLevel.emb v x.1) g) ∧
      z = (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x.1 g z then h.2.choose_spec.choose else 1) := by
    intro P
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · obtain ⟨g, z, hrel, hin⟩ := H.1 P v hP _ (((K (chOf c)).lev.U_eq _).1 (GlobalTheory.Mem.Col2.ChartLevel.embU _ v x).2).1 hx
      have hnp : NearPair I l Z a v P x.1 g z := by
        refine ⟨?_, ?_⟩
        · have hmid := hrel.1
          unfold MidAt at hmid
          rw [key P _ (by omega)] at hmid
          exact hmid
        · have hin' := hin
          unfold NearV
          unfold GlobalTheory.TwU.InFrame at hin'
          rw [hfb1 P hP] at hin'
          first
            | (simp only [GlobalTheory.TwU.ratA, map_one, inv_one, one_mul, mul_one] at hin'; exact hin')
            | (erw [map_one, inv_one, one_mul, mul_one] at hin'; exact hin')
            | (convert hin' using 2; simp)
      have hh : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x.1 g z := ⟨hP, g, z, hnp⟩
      refine ⟨g, z, ⟨hrel, hin⟩, ?_⟩
      rw [dif_pos hh]
      exact nearPair_val_unique I hOk l Z a v P x.1 _ _ _ _ hnp hh.2.choose_spec.choose_spec
    · refine ⟨1, 1, ⟨⟨LocVal.midLev_one_one I hOk a _ hm _ P, fun _ t => ?_⟩, ?_⟩, by rw [dif_neg (fun h => hP (And.left h))]⟩
      · have e : ((1 : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (y0 P) - y0 P) t = 0 := by
          show (y0 P - y0 P) t = 0
          rw [sub_self]; rfl
        rw [e, mul_zero]
        simpa using GlobalTheory.TopInv.intAt_nat (P := P.1) 0
      · unfold GlobalTheory.TwU.InFrame
        exact LocVal.nearAt_emb_one v _ hP _ _ _ _ (map_one (GlobalTheory.TwU.seamGL (sm I l Z)))
  choose gg zz hgz hz using hall
  have hc := H.2.2 (GlobalTheory.Mem.Col2.ChartLevel.embU _ v x) gg zz hgz
  unfold valV
  rw [← Finset.prod_congr rfl fun P _ => hz P]
  exact hc

end GlobalTheory.Mem.Col2.QChi

end
end

