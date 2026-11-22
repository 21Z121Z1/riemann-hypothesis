import Formalism.LocalToGlobal.Columns.Bundle0032
import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.RecordInst
import Formalism.LocalToGlobal.Columns.TwQDefs
import Formalism.LocalToGlobal.Columns.Bundle0031
import Formalism.LocalToGlobal.Columns.RecLevelCls

-- bundled from Formalism.LocalToGlobal.Columns.TiedXpU
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem lastVector_eq_single (n : ℕ) (p : E) : z0 E n p = (Pi.single (lastIdx (n + 1)) p : Fin (n + 1) → E) := by
  have hl : lastIdx (n + 1) = Fin.last n := Fin.ext (by simp [lastIdx])
  rw [hl]
  funext j
  simp [z0, eLast, Pi.single_apply]

theorem xp_tilH_f {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG : Finset (Pl E)} (d : DecoSet E n ∅ SG) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) {b : 𝓞 E} (hb : SepElt ST b) (P : ST)
    (y : Sp E N) (hy : y ∈ (DecoSet.tilH (ST := ST) hN pi d).1.Lsh) (r : 𝓞 E)
    (hr : algebraMap (𝓞 E) E r = hStd E N (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi)) y) :
    (DecoSet.tilH (ST := ST) hN pi d).1.f P y = Ideal.Quotient.mk P.1.asIdeal r := by
  subst hN
  have hy' : y ∈ (DecoSet.til (ST := ST) pi d).1.Lsh := hy
  have h1 : y ∈ localization₂ P.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N := by
    rw [← (DecoSet.til (ST := ST) pi d).2.locP_Lsh hb P]
    exact le_locP _ _ hy'
  show (DecoSet.til (ST := ST) pi d).1.f P y = _
  rw [DecoSet.til_val d hT hG] at h1 ⊢
  have h2 : (d.1.til (ST := ST) pi).f P y = redP P.1 (hStd E (n + 1) (z0 E n (algebraMap (𝓞 E) E pi)) y) := if_pos h1
  rw [h2, lastVector_eq_single, ← hr, reduction_coe]

theorem xp_til_f_core {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG SG' : Finset (Pl E)} (hSG : SG ⊆ SG') {H : Subgroup (GLG E N SG)}
    (d : DecoSet E n ∅ SG') {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG', pi ∉ w.1.asIdeal) {b : 𝓞 E}
    (hb : SepElt ST b) (g : UF E N × H) (e : DecoSet E N ST SG) (hge : g • e = (DecoSet.tilH (ST := ST) hN pi d).res hSG) (P : ST)
    (x : Sp E N) (hx : x ∈ e.1.Lsh) (r : 𝓞 E)
    (hr : algebraMap (𝓞 E) E r = hStd E N (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi)) (g.1.1 x)) :
    e.1.f P x = Ideal.Quotient.mk P.1.asIdeal r := by
  have h1 : e.1.f P x = (g • e).1.f P (g.1.1 x) := by
    show _ = e.1.f P (g.1.1.symm (g.1.1 x))
    rw [LinearEquiv.symm_apply_apply]
  have h2 : g.1.1 x ∈ (g • e).1.Lsh := by
    rw [rlc_smul_val, Deco.Lsh_act _ g.1.2]
    exact Submodule.mem_map_of_mem hx
  rw [h1]
  rw [hge] at h2 ⊢
  exact xp_tilH_f hN d hT hG hb P _ h2 r hr

end Gen

section GenJ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem xp_hform_one (hc : CMData F E) {N : ℕ} (x y : Fin N → E) :
    hform (hc.sig : E →+* E) (1 : Matrix (Fin N) (Fin N) E) x y = hStd E N x y := by
  unfold hform
  rw [hStd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
    rfl
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem xp_til_f_coreJ (hc : CMData F E) {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG SG' : Finset (Pl E)} (hSG : SG ⊆ SG')
    {H : Subgroup (GLG E N SG)} (d : DecoSet E n ∅ SG') {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal)
    (hG : ∀ w : SG', pi ∉ w.1.asIdeal) {b : 𝓞 E} (hb : SepElt ST b) (g : UF E N × H) (e : DecoSet E N ST SG)
    (hge : g • e = (DecoSet.tilH (ST := ST) hN pi d).res hSG) (P : ST) (x : Sp E N) (hx : x ∈ e.1.Lsh) (r : 𝓞 E)
    {J : Matrix (Fin N) (Fin N) E} (hJ : J = 1)
    (hr : algebraMap (𝓞 E) E r = hform (hc.sig : E →+* E) J (Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi))
      ((((ratEquiv hc N).symm g.1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)) :
    e.1.f P x = Ideal.Quotient.mk P.1.asIdeal r := by
  subst hJ
  refine xp_til_f_core hN hSG d hT hG hb g e hge P x hx r ?_
  rw [hr, xp_hform_one, ← rlc_ratHom_apply hc N]
  have : ratHom hc N ((ratEquiv hc N).symm g.1) = g.1 := (ratEquiv hc N).apply_symm_apply g.1
  rw [this]

end GenJ

section GenQ

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

section Step

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

theorem xp_clsG_U : (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.U = levU hc n (Pr.vT u) Pr.vGs Λ.grp := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

theorem xp_clsG_chi (x : (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.U) (hx : x.1 ∈ levU hc n (Pr.vT u) Pr.vGs Λ.grp) :
    (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.chi x = levTyp ((Units.map σ₀.toMonoidHom).comp Λ.chr) ⟨x.1, hx⟩ := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

theorem xp_clsG_y (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp) :
    ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).y c).1 = (ptOfD hc n (Pr.vT u) Pr.vGs c₀ (s c)).1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

end Step

section P

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet X.E n (∅ : Finset (Pl X.E)) Pr.vGs)
  (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.N)

theorem xp_clsPG_y (c : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp) :
    ((clsPG hc σ₀ Λ s hS hs Q).y c).1 = (ptOfD hc n ∅ Pr.vGs 1 (s c)).1 := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  rfl

end P

end GenQ

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)

abbrev ColDat.tilC (d : ColDat) (u : d.what₂.Word) (c : PCl d) : StCl (Pr := d.Pr) d.W d.lev u d.R.m :=
  tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c

theorem tilGa_mulVec (u : d.what₂.Word) (c : PCl d) (x : Fin (d.R.N d.R.m) → d.host.E) :
    ((d.tilGa u c : GL (Fin (d.R.N d.R.m)) d.host.E) : Matrix _ _ d.host.E) *ᵥ x = (d.tilMv u c).1.1 x := by
  rw [← rlc_ratHom_apply d.sp.cm (d.R.N d.R.m)]
  have : ratHom d.sp.cm (d.R.N d.R.m) (d.tilGa u c) = (d.tilMv u c).1 :=
    (ratEquiv d.sp.cm (d.R.N d.R.m)).apply_symm_apply _
  rw [this]

include hS hH in
set_option maxHeartbeats 1000000 in

theorem xp_Ld_eq (u : d.what₂.Word) (c : StCl (Pr := d.Pr) d.W d.lev u d.R.m) :
    CF.Ld (d.colRec a) u d.R.m le_rfl c = (d.repr u d.R.m c).1.Lsh :=
  tie_Ld_eq (X := d.X) (Pr := d.Pr) d.sp.cm d.σ₀ u (d.repr u d.R.m) (stepCrd a hS hH u d.R.m le_rfl) c

variable (hP : PtSurjP d)

set_option maxHeartbeats 2000000 in

def tildeLatticeAgreement (u : d.what₂.Word) :
    CF.TilTied (D := d.colRec a) u (atTTied a hH u) (parabolicClassAgreement a hS hH hP u) (levelAgreement a hS hH u d.R.m le_rfl) where
  z0 := d.z0 u
  lastCoordinateUniformizerVector_spans_orthogonal_line := lastCoordinateUniformizerVector_spans_orthogonal_line a hS u
  hermitianForm_lastCoordinateUniformizerVector_self := hermitianForm_lastCoordinateUniformizerVector_self a hS u
  ga := tieGa a hS u
  til_lat := til_lat a hS u
  til_fv := fun v c x r hr =>
    (tie_fv d.sp.cm d.hPr d.σ₀ u (d.repr u d.R.m) (stepCrd a hS hH u d.R.m le_rfl) v (d.tilC u c) x).trans
      (xp_til_f_coreJ d.sp.cm (N_m_succ d.R) (Finset.Subset.refl _) (d.reprP c) (fun P => conj_piT_notMem d.hPr u P)
        (a.piT_off u) (sepElt_of_ok d.hPr u) (d.tilMv u c) _ (tilMv_smul u c) v x.1 ((xp_Ld_eq a hS hH u (d.tilC u c)).le x.2) r
        (gramN_eq a hS d.R.m le_rfl) hr)

def TilMove (u : d.what₂.Word) : Prop :=
  ∀ c : PCl d, ∃ κ : levU d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp,
    levRed d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp κ = (d.tilMv u c).2 ∧
    ∀ g : GL (Fin (d.R.N d.R.m)) (d.host.E ⊗[d.host.F] FiniteAdeleRing (𝓞 d.host.F) d.host.F),
      CF.IsExt (d.colRec a) (d.z0 u) (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F))
        (ptOfD d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs 1 (d.reprP c)).1.1 g.1 →
      bc (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F)) (d.tilGa u c).1 *
        (ptOfD d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m)
          (d.repr u d.R.m (d.tilC u c))).1 = g * κ.1

variable (hQ : PtSurj d)

def tilAd (u : d.what₂.Word) (hM : TilMove a u) :
    CF.TilAd (tildeLatticeAgreement a hS hH hP u) (classAgreement a hS hH hQ u d.R.m le_rfl) where
  ka := fun c => ⟨(hM c).choose.1, (Subgroup.ext_iff.1 (xp_clsG_U d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m)
    (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m) (hQ u d.R.m)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl)) _).2 (hM c).choose.2⟩
  til_ad := fun c g hg => by
    have h1 := xp_clsPG_y d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c)
      (crdPr a hS hH) c
    have h2 := xp_clsG_y d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
      (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl) (d.tilC u c)
    have hg' : CF.IsExt (d.colRec a) (d.z0 u) (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F))
        (ptOfD d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs 1 (d.reprP c)).1.1 g.1 := by
      rw [← h1]; exact hg
    have h3 := (hM c).choose_spec.2 g hg'
    exact (congrArg (fun t => bc (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F)) (d.tilGa u c).1 * t) h2).trans h3

def tieEWz (u : d.what₂.Word) : ((d.colRec a).mem u).P.Wz ≃ₗ[ℂ]
    (((d.colRec a).fm u).clsP → ((d.colRec a).mem u).C.Y d.R.m → ℂ) := LinearEquiv.refl _ _

def PerOnto (d : ColDat) (a : ColArgs d) : Prop :=
  (∀ z ∈ (ptEv (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx).Fi, ∃ F, jMCL (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk F = z) ∧
    ∀ F, jMCL (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk F ∈ (ptEv (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx).Fi

def tieJM (u : d.what₂.Word) : ((d.colRec a).mem u).P.Mt →ₛₗ[starRingEnd ℂ] ((d.colRec a).mem u).P.Wrow :=
  jMCL (Pr := d.Pr) d.W d.levP d.σ₀ d.star_cx a.rowOk

theorem perTied (u : d.what₂.Word) (hO : PerOnto d a) : CF.PerTie (D := d.colRec a) u (tieJM a u) :=
  ⟨hO.1, hO.2, fun w F => periodC_eq_ipCl' (Pr := d.Pr) d.W d.levP d.hX d.σ₀ d.star_cx a.rowOk w F⟩

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQSurj
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG

section QSurj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

variable (ST SG Q) in

structure QOff : Prop where
  off : ∀ (P : Q) (P' : Pl E), P' ∈ ST ∨ P' ∈ SG → ¬ IsOver (qv F P.1) P'
  inj : ∀ P P' : Q, qv F P.1 = qv F P'.1 → P = P'

def QIntGL {v : HeightOneSpectrum (𝓞 F)} (k : GL (Fin n) (v.adicCompletion F)) : Prop :=
  (∀ i j, ((k : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, (((k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) ∈ v.adicCompletionIntegers F)

variable (ST SG) in

def FrLat (q : QLoc hc n Q Θ) : Prop :=
  ∀ (x : UAd hc n) (p : DecoF E n ST SG Q), decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = p.deco → ∀ P : Q,
    QIntGL ((bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x)

def QLift (q : QLoc hc n Q Θ) : Prop :=
  ∀ (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)), QIntGL k →
    ∃ κ : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F),
      κ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) ((qv F P.1).adicCompletion F) ∧
      κ ∈ stabGL (Formalism.L2.Herm.locL (qv F P.1) (stdLat E n)) ∧
      bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) κ = k

theorem qdf_at_put_ne (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : qv F P.1 ≠ v) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : q.at P (x * rll_put n v g) = q.at P x := by
  show bc _ (bc (prV (E := E) (qv F P.1)) (x * rll_put n v g)) = _
  rw [map_mul, rll_put_ne n v (qv F P.1) hv g, mul_one]

theorem qdf_at_put_self (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (g : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F)) :
    q.at P (x * rll_put n (qv F P.1) g) = q.at P x * bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) g := by
  show bc _ (bc (prV (E := E) (qv F P.1)) (x * rll_put n (qv F P.1) g)) = _
  rw [map_mul, rll_put_self, map_mul]

theorem qdf_inv_mem_UPts {v : HeightOneSpectrum (𝓞 F)} {κ : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (h : κ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)) :
    κ⁻¹ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := inv_mem h

theorem qdf_inv_mem_stab {v : HeightOneSpectrum (𝓞 F)} {κ : GL (Fin n) (E ⊗[F] v.adicCompletion F)}
    (h : κ ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))) : κ⁻¹ ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := inv_mem h

theorem exists_adelic_point_of_local_frames (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hL : QLift q)
    (p : DecoF E n ST SG Q) (S : Finset Q) :
    ∃ x : UAd hc n, decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = p.deco ∧
      ∀ P ∈ S, (bc (q.phi P) (qGL n (p.fr P)))⁻¹ * q.at P x ∈ q.U P := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨ptOf hc n ST SG p.deco, decoOf_ptOf hc n ST SG hS p.deco, fun P hP => absurd hP (Finset.notMem_empty P)⟩
  | insert P S hPS ih =>
    obtain ⟨x, hx, hxS⟩ := ih
    obtain ⟨κ, hκU, hκS, hκ⟩ := hL P _ (hF x p hx P)
    have hput : rll_put n (qv F P.1) κ⁻¹ ∈ K1 hc n ST SG :=
      put_mem_kOne_of_not_over ST SG (fun P' hP' => hQ.off P P' (Or.inl hP'))
        (fun P' hP' => hQ.off P P' (Or.inr hP'))
        (rll_put_mem_UAd hc n (qv F P.1) (qdf_inv_mem_UPts hκU)) (qdf_inv_mem_stab hκS)
    have hputU : rll_put n (qv F P.1) κ⁻¹ ∈ UAd hc n := rll_put_mem_UAd hc n (qv F P.1) (qdf_inv_mem_UPts hκU)
    refine ⟨x * ⟨_, hputU⟩, ?_, ?_⟩
    · show decoOf ST SG ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * rll_put n (qv F P.1) κ⁻¹) = _
      rw [decoration_mul_principal hc n ST SG _ hput, hx]
    · intro P' hP'
      show (bc (q.phi P') (qGL n (p.fr P')))⁻¹ * q.at P' ((x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * rll_put n (qv F P.1) κ⁻¹) ∈ q.U P'
      rcases Finset.mem_insert.1 hP' with rfl | hP'
      · rw [qdf_at_put_self, map_inv, hκ, ← mul_assoc, mul_inv_cancel]
        exact one_mem _
      · have hne : qv F P'.1 ≠ qv F P.1 := fun h => hPS (hQ.inj P' P h ▸ hP')
        rw [qdf_at_put_ne q P' _ _ hne]
        exact hxS P' hP'

theorem decoPtSurjF_of (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hL : QLift q) :
    DecoPtSurjF hc n ST SG Q q := by
  classical
  intro p
  obtain ⟨x, hx, hxS⟩ := exists_adelic_point_of_local_frames hS hQ q hF hL p Finset.univ
  exact ⟨x, hx, fun P => hxS P (Finset.mem_univ P)⟩

end QSurj

end Formalism.L2.Col
end
end

