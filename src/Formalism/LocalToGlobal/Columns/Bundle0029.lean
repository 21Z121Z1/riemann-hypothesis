import Formalism.LocalToGlobal.Columns.Bundle0027
import Formalism.LocalToGlobal.Columns.Bundle0022
import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.RecLevelLocF
import Formalism.LocalToGlobal.Columns.Bundle0028
import Formalism.LocalToGlobal.Columns.Bundle0018

-- bundled from Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

theorem th_gram_eq (hS : SpStd d.toColBase) (i : ℕ) (hi : i ≤ d.R.m) : (d.sp.X i).gram = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X i).hT ((d.sp.X i).frame x) ((d.sp.X i).frame y) = _
  rw [hS.X_on i hi, Matrix.one_apply]

theorem th_gram0_eq (hS : SpStd d.toColBase) : d.sp.gram0 = 1 := by
  refine Matrix.ext fun x y => ?_
  show (d.sp.X 0).hT ((d.sp.X 0).frame _) ((d.sp.X 0).frame _) = _
  rw [hS.X_on 0 (Nat.zero_le _), Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

theorem th_crdLat_eq (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    Formalism.L2.Herm.crdLat (d.sp.X i) (d.clsLat u i c) = Formalism.L2.Forms.reL (d.sp.X_rank i hi).symm (d.repr u i c).1.L := by
  unfold Formalism.L2.Herm.crdLat ColDat.clsLat Formalism.L2.Forms.reL
  rw [dif_pos hi, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show (d.sp.X i).frame.equivFun ((d.crd i hi).symm x) j = _
  unfold ColDat.crd
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem th_crdLat0_eq (u : d.what₂.Word) (c : StCl (Pr := d.Pr) d.W d.lev u 0) :
    d.sp.crdLat0 (d.clsLat u 0 c) = Formalism.L2.Forms.reL (Formalism.L2.Forms.rank_eq_first_level d.R).symm (d.repr u 0 c).1.L := by
  unfold Spaces.crdLat0 ColDat.clsLat Formalism.L2.Forms.reL
  rw [dif_pos (Nat.zero_le _), ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show d.sp.crd0 ((d.crd 0 (Nat.zero_le _)).symm x) j = _
  unfold ColDat.crd Spaces.crd0
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

def hCrd (hS : SpStd d.toColBase) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    HCrd d.Pr (d.R.N i) fun c : StCl (Pr := d.Pr) d.W d.lev u i => (d.repr u i c).1.L where
  n' := (d.sp.X i).rank
  hn := d.sp.X_rank i hi
  J := (d.sp.X i).gram
  hJ := th_gram_eq hS i hi
  f := d.R.f
  hf := d.f_eq.symm
  bad := plUnder d.X.F d.Pr.vGs
  hbad := rfl
  lat := fun c => Formalism.L2.Herm.crdLat (d.sp.X i) (d.clsLat u i c)
  hlat := fun c => th_crdLat_eq u i hi c

def hCrd0 (hS : SpStd d.toColBase) (u : d.what₂.Word) :
    HCrd d.Pr (d.R.N 0) fun c : StCl (Pr := d.Pr) d.W d.lev u 0 => (d.repr u 0 c).1.L where
  n' := d.R.k
  hn := Formalism.L2.Forms.rank_eq_first_level d.R
  J := d.sp.gram0
  hJ := th_gram0_eq hS
  f := d.R.f
  hf := d.f_eq.symm
  bad := plUnder d.X.F d.Pr.vGs
  hbad := rfl
  lat := fun c => d.sp.crdLat0 (d.clsLat u 0 c)
  hlat := fun c => th_crdLat0_eq u c

def LocalLevelIsKOneEverywhere (d : ColDat) : Prop := ∀ (u : d.what₂.Word) (i : ℕ), LocalLevelIsKOneAtT d.sp.cm u (d.lev i)

def IwAll (d : ColDat) (S : GSplit (Pr := d.Pr) d.sp.cm) : Prop := ∀ u : d.what₂.Word, IwLoc d.sp.cm u (d.lev 0) S.sp

def hermPack (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :=
  levPack d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hi)

def hermPack0 (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (u : d.what₂.Word) :=
  levPack d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u)

def hermLev0 (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
    (u : d.what₂.Word) :
    ColLevel d.R d.host.F d.host.E d.sp d.host.g (d.chain a u) (d.atT a u) (fun i c => d.clsLat u i c) :=
  LevPack.toCol (sp := d.sp) (C := d.chain a u) (A := d.atT a u) (clsLat := fun i c => d.clsLat u i c)
    (hermPack0 hS hP hK u) S.sp S.sp_sig
    (levPack_iw d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) S.sp _ _ _ _ _ (hI u) (hCrd0 hS u))
    (exists_place_over_first_prime d.hX d.hPr).choose (exists_place_over_first_prime d.hX d.hPr).choose_spec

def hermCols (hS : SpStd d.toColBase) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S) :
    CH.HermCols (d.colRec a) where
  lev0 := fun u => hermLev0 a hS hP hK S hI u
  lev := fun u i _ hm => LevPack.toStep (S := d.sp.X i) (lat := d.clsLat u i) (hermPack hS hP hK u i hm)
  cls := fun u i _ hm => LevPack.toCls (S := d.sp.X i) (lat := d.clsLat u i) (hermPack hS hP hK u i hm)
  vT := fun u => tieEV d.sp.cm d.hX d.hPr u
  Fv := fun u v => tieFv d.sp.cm d.hX d.hPr u v

theorem stdTied (hS : SpStd d.toColBase) : CH.StdTied (d.colRec a) :=
  ⟨fun i hi => ⟨(d.sp.X i).frame, hS.X_on i hi, hS.selfDual_span_frame_X i hi⟩, ⟨d.sp.X'.frame, hS.P_on, hS.selfDual_span_frame_auxiliary⟩⟩

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedFv
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.UG.P

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

theorem fv_rho_prV {P : Pl E} (hov : IsOver v P) (β : Formalism.L2.Herm.intAf F E) :
    rll_rho v P ⟨prV (E := E) v (β : E ⊗[F] Formalism.L2.Herm.Af F), afsplit_prV_int v _ β.2⟩ = resS F P β := by
  show resS F P ⟨afsplitIE v (prV (E := E) v (β : E ⊗[F] Formalism.L2.Herm.Af F)), _⟩ = resS F P β
  rw [← sub_eq_zero, ← map_sub]
  refine resS_eq_zero_of_prV P v hov _ ?_
  show prV (E := E) v (afsplitIE v (prV (E := E) v (β : E ⊗[F] Formalism.L2.Herm.Af F)) - (β : E ⊗[F] Formalism.L2.Herm.Af F)) = 0
  rw [map_sub, afsplit_prV_IE, sub_self]

theorem fv_prV_pullV (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (z : Fin n → E) (i : Fin n) :
    prV (E := E) v (pullV y z i) =
      (((bc (prV (E := E) v) y)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)).1 *ᵥ
        fun a => inclE (F := F) (v.adicCompletion F) (z a)) i := by
  unfold pullV
  rw [← map_inv]
  simp only [Matrix.mulVec, dotProduct]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, afsplit_prV_inclE]
  rfl

variable (h : BasePi ST π)

theorem fv_psi_pull {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (z : Fin n → E)
    (hz : cO E π • z ∈ Formalism.UG.CS.globLat y (stdLat E n))
    (ht : (((bc (prV (E := E) v) y)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)).1 *ᵥ
        fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ baseDualV hc n ST v) :
    rll_psi hc n v h P ⟨_, ht⟩ = Ideal.Quotient.mk P.asIdeal (cO E π) * redA P (pullV y z (lastIdx n)) := by
  have hm : iA F E (algebraMap (𝓞 E) E (cO E π)) * pullV y z (lastIdx n) ∈ Formalism.L2.Herm.intAf F E := by
    rw [← pullV_osmul]
    exact (mem_globLat y _).1 hz _
  rw [redA_spec P (h.conj_notMem hP) hm, ← fv_rho_prV v hov]
  show rll_rho v P _ = rll_rho v P _
  congr 1
  apply Subtype.ext
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π)) * _ =
    prV (E := E) v (iA F E (algebraMap (𝓞 E) E (cO E π)) * pullV y z (lastIdx n))
  rw [map_mul, afsplit_prV_inclE, fv_prV_pullV, algebraMap_cO]

def fvPsiEquiv {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P) :
    fMod hc n ST v ≃+ kP P :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext x
    rw [AddMonoidHom.mem_ker, rll_psi_ker hc n v h hP huniq]
    rfl : ((Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (baseKer E n ST)).comap
      (baseDualV hc n ST v).subtype).toAddSubgroup = (rll_psi hc n v h P).ker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (rll_psi_surj hc n v h hov))

def fvMulEquiv {R : Type} [CommRing R] (a b : R) (hab : a * b = 1) : R ≃+ R where
  toFun x := a * x
  invFun x := b * x
  left_inv x := by
    show b * (a * x) = x
    rw [← mul_assoc, mul_comm b a, hab, one_mul]
  right_inv x := by
    show a * (b * x) = x
    rw [← mul_assoc, hab, one_mul]
  map_add' := mul_add _

def fvMeL {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P)
    (a b : 𝓞 E ⧸ P.asIdeal) (hab : a * b = 1) : fMod hc n ST v ≃+ (𝓞 E ⧸ P.asIdeal) :=
  (fvPsiEquiv hc n v h hP hov huniq).trans (fvMulEquiv a b hab)

theorem fvMeL_fLoc {P : Pl E} (hP : P ∈ ST) (hov : IsOver v P) (huniq : ∀ Q ∈ ST, IsOver v Q → Q = P)
    (a b : 𝓞 E ⧸ P.asIdeal) (hab : a * b = 1) (x : baseDualV hc n ST v) :
    fvMeL hc n v h hP hov huniq a b hab (fLoc hc n ST v x) = a * rll_psi hc n v h P x := rfl

variable (SG : Finset (Pl E)) (c₀ : DiaG E ST)

omit h in

theorem fv_f_eq (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hyU : y ∈ UAd hc n) (d : DecoSet E n ST SG)
    (hd : decoOfD n ST SG c₀ y = d) (P : ST) (z : Sp E n) (hz : z ∈ d.1.at P.1) :
    d.1.N = Formalism.UG.CS.globLat y (stdLat E n) ∧ d.1.f P z = (c₀ P).1 * redA P.1 (pullV y z (lastIdx n)) := by
  classical
  have hval : d.1 = (decoRaw ST SG y).dia c₀ := by
    rw [← hd, ← rlc_decoOf_val hc n ST SG hyU]
    rfl
  have hN : d.1.N = Formalism.UG.CS.globLat y (stdLat E n) := by rw [hval]; rfl
  refine ⟨hN, ?_⟩
  have hloc : z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) := by
    rw [← hN]; exact hz
  rw [hval]
  show (c₀ P).1 * (if z ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat y (stdLat E n)) then
    redA P.1 (pullV y z (lastIdx n)) else 0) = _
  rw [if_pos hloc]

theorem fv_tieL (ha : SepElt ST (cO E π)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hyU : y ∈ UAd hc n)
    (d : DecoSet E n ST SG) (hd : decoOfD n ST SG c₀ y = d) (P : ST) (hov : IsOver v P.1) {t : 𝓞 E}
    (htt : cO E π * t - 1 ∈ P.1.asIdeal) (z : Sp E n) (hzL : z ∈ d.1.Lsh)
    (ht : (((bc (prV (E := E) v) y)⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)).1 *ᵥ
        fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ baseDualV hc n ST v) :
    d.1.f P z = (c₀ P).1 * Ideal.Quotient.mk P.1.asIdeal t * rll_psi hc n v h P.1 ⟨_, ht⟩ := by
  obtain ⟨hN, hf⟩ := fv_f_eq hc n SG c₀ y hyU d hd P z (d.2.Lsh_le_at ha P hzL)
  have hzN : cO E π • z ∈ Formalism.UG.CS.globLat y (stdLat E n) := by
    rw [← hN]
    exact d.2.smul_Lsh_mem_N ha.conj hzL
  have h1 : Ideal.Quotient.mk P.1.asIdeal t * Ideal.Quotient.mk P.1.asIdeal (cO E π) = 1 := by
    rw [← map_mul, mul_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk P.1.asIdeal), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 htt
  rw [hf, fv_psi_pull hc n v h P.2 hov y z hzN ht, mul_assoc, ← mul_assoc (Ideal.Quotient.mk P.1.asIdeal t), h1, one_mul]

end Loc

section Dec

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem fv_unit (P : Pr.vT u) :
    (c₀ P).1 * Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) *
      (Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) * (c₀ P).inv) = 1 := by
  have h1 : Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) * Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) = 1 := by
    rw [← map_mul, mul_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk P.1.asIdeal), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (tieInv_spec hPr u P)
  rw [mul_assoc, ← mul_assoc (Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P)), h1, one_mul]
  exact (c₀ P).val_inv

def fvMe (P : Pr.vT u) : fMod hc n (Pr.vT u) (tieEV hc hX hPr u P).1 ≃+ (𝓞 X.E ⧸ P.1.asIdeal) :=
  fvMeL hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) P.2 (tieEV_over hc hX hPr u P)
    ((basePi_of_ok hX hPr u).over_unique hc P.2 (tieEV_over hc hX hPr u P)) _ _ (fv_unit hPr u c₀ P)

theorem fv_tie₁ (y : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) (hyU : y ∈ UAd hc n) (d : DecoSet X.E n (Pr.vT u) Pr.vGs)
    (hd : decoOfD n (Pr.vT u) Pr.vGs c₀ y = d) (P : Pr.vT u) (z : Sp X.E n) (hzL : z ∈ d.1.Lsh)
    (ht : (((bc (prV (E := X.E) (tieEV hc hX hPr u P).1) y)⁻¹ :
          GL (Fin n) (X.E ⊗[X.F] (tieEV hc hX hPr u P).1.adicCompletion X.F)).1 *ᵥ
        fun a => inclE (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (z a)) ∈
      baseDualV hc n (Pr.vT u) (tieEV hc hX hPr u P).1) :
    d.1.f P z = fvMe hc hX hPr u c₀ P (fLoc hc n (Pr.vT u) (tieEV hc hX hPr u P).1 ⟨_, ht⟩) :=
  fv_tieL hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) Pr.vGs c₀ (sepElt_of_ok hPr u) y hyU d hd P
    (tieEV_over hc hX hPr u P) (tieInv_spec hPr u P) z hzL ht

variable (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

def tieFMe (P : Pr.vT u) :
    (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.fM (tieEV hc hX hPr u P).1 (tieEV hc hX hPr u P).2 ≃+ (𝓞 X.E ⧸ P.1.asIdeal) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact fvMe hc hX hPr u c₀ P

set_option maxHeartbeats 1000000 in

theorem tie_FvTie (P : Pr.vT u) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp)
    (z : ↥(Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (hz : ((bc (prV (E := X.E) (tieEV hc hX hPr u P).1) ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (z.1 a)) ∈
      latS (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (intV X.E (tieEV hc hX hPr u P).1)
        (Submodule.span (𝓞 X.E) (dualSet (hc.sig : X.E →+* X.E) Q.J (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Lb))) :
    (s c).fv P (tiePr hc hPr σ₀ u s Q P c z) =
      tieFMe hc hX hPr σ₀ u Λ c₀ s hS hs Q P
        ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.fT (tieEV hc hX hPr u P).1 (tieEV hc hX hPr u P).2 ⟨_, hz⟩) := by
  have hzL : z.1 ∈ (s c).1.Lsh := (tie_Ld_eq hc σ₀ u s Q c) ▸ z.2
  refine (tie_fv hc hPr σ₀ u s Q P c z).trans ?_
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact fv_tie₁ hc hX hPr u c₀ _ (ptOfD hc n (Pr.vT u) Pr.vGs c₀ (s c)).2 (s c)
    (decoOfD_ptOfD hc n (Pr.vT u) Pr.vGs hS c₀ (s c)) P z.1 hzL hz

end Dec

section Rec

variable {d : ColDat} (a : ColArgs d)

def formModuleEquivAtPlace (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m)
    (v : ((d.colRec a).mem u).A.vT) :
    (classAgreement a hS hH hP u i hi).lev.fM ((atTTied a hH u).eV v).1 ((atTTied a hH u).eV v).2 ≃+ ((d.colRec a).mem u).A.Fv v :=
  tieFMe d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi) v

set_option maxHeartbeats 1000000 in

theorem fvTied (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    CF.FvTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (formModuleEquivAtPlace a hS hH hP u i hi) :=
  fun v c z hz =>
    tie_FvTie d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
      (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (stepCrd a hS hH u i hi) v c z hz

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlExt
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.UG Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hCh : d.Ch.Ok)
  (hl : d.lev = colLevS d.Ch) (hlP : d.levP = (rowTyG d.Ch (rPsharp d.Ch)).inv)

set_option maxHeartbeats 1000000 in

theorem recFrExt (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hP' : PtSurjP d) (u : d.what₂.Word)
    (hiX : ∀ (y : Fin (d.R.N d.R.m - 1) → d.host.E) (x : Fin (d.R.N d.R.m)),
      CF.iXc (d.colRec a) y x = if h : (x : ℕ) < d.R.N d.R.m - 1 then y ⟨x, h⟩ else 0) :
    CF.FrExt (D := d.colRec a) (u := u) (Pi.single (lastIdx (d.R.N d.R.m)) (d.piT u : d.host.E))
      (recGLev a S hCh hl hS hH hP u d.R.m le_rfl) (recGLevP a S hCh hlP hS hH hP' u) := by
  intro i v h
  have e1 : (recGLev a S hCh hl hS hH hP u d.R.m le_rfl).fr i v h = glvD (d.R.N d.R.m) v (recUnit S u d.R.m i v h) :=
    congrFun (congrFun (congrFun (recGLev_fr a S hCh hl hS hH hP u d.R.m le_rfl) i) v) h
  have e2 : (recGLevP a S hCh hlP hS hH hP' u).fr i v h = 1 :=
    congrFun (congrFun (congrFun (recGLevP_fr a S hCh hlP hS hH hP' u) i) v) h
  have hD : ∀ x y : Fin (d.R.N d.R.m), (glvD (d.R.N d.R.m) v (recUnit S u d.R.m i v h)).1 x y =
      if x = y then ((glvU (d.R.N d.R.m) v (recUnit S u d.R.m i v h) x : v.adicCompletionIntegers d.X.F) : v.adicCompletion d.X.F)
        else 0 := fun x y => Matrix.diagonal_apply _ x y
  constructor
  · intro (x : Fin (d.R.N d.R.m)) (b : Fin (d.R.N d.R.m - 1)) (b' : Fin (d.R.N d.R.m)) (hb : (b : ℕ) = b')
    rw [e1, e2, hD, Units.val_one, Matrix.mul_one, Matrix.map_apply]
    have hx : CF.iXm (d.colRec a) x b = if x = b' then 1 else 0 := by
      show LinearMap.toMatrix' (CF.iXc (d.colRec a)) x b = _
      rw [LinearMap.toMatrix'_apply, hiX]
      by_cases hxb : x = b'
      · subst hxb
        have hlt : (x : ℕ) < d.R.N d.R.m - 1 := by rw [← hb]; exact b.2
        have hbx : (⟨(x : ℕ), hlt⟩ : Fin (d.R.N d.R.m - 1)) = b := Fin.ext hb.symm
        rw [if_pos rfl, dif_pos hlt, hbx, Pi.single_eq_same]
      · rw [if_neg hxb]
        by_cases h1 : (x : ℕ) < d.R.N d.R.m - 1
        · rw [dif_pos h1, Pi.single_eq_of_ne]
          intro h2
          apply hxb
          apply Fin.ext
          rw [← hb, ← h2]
        · rw [dif_neg h1]
    rw [hx]
    by_cases hxb : x = b'
    · rw [if_pos hxb, if_pos hxb, map_one]
      have hne : x ≠ lastIdx (d.R.N d.R.m) := by
        intro hl
        have h3 : (x : ℕ) = d.R.N d.R.m - 1 := by rw [hl]; rfl
        have h4 := b.2
        rw [hxb, ← hb] at h3
        omega
      unfold glvU
      rw [if_neg hne]
      rfl
    · rw [if_neg hxb, if_neg hxb, map_zero]
  · intro (x : Fin (d.R.N d.R.m)) (l : Fin (d.R.N d.R.m)) (hl : (l : ℕ) + 1 = d.R.N d.R.m)
    have hll : l = lastIdx (d.R.N d.R.m) := Fin.ext (by show (l : ℕ) = d.R.N d.R.m - 1; omega)
    rw [e1, hD, hll, Pi.single_apply]
    by_cases hx : x = lastIdx (d.R.N d.R.m)
    · rw [if_pos hx, if_pos hx]
      unfold glvU recUnit
      rw [if_pos hx, if_pos rfl]
      rfl
    · rw [if_neg hx, if_neg hx, map_zero, map_zero]

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedValBwP
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ)

include hX in

theorem mem_localization_stepLattice_iff (w : HeightOneSpectrum (𝓞 X.K)) (v : {P // P ∈ Pr.vT u}) (x : (stepGSD W Λ u i).EqFun) :
    x ∈ localization₂ w.asIdeal (stepBv W Λ u i v) ↔ ∀ c : StCl W Λ u i,
      (x : (stepGSD W Λ u i).D → (stepGSD W Λ u i).V) ((stepGSD W Λ u i).outSec.rep c) ∈
        localization₂ w.asIdeal (BvLat W u i v ((stepGSD W Λ u i).outSec.rep c)) := by
  constructor
  · rintro ⟨t, ht, h⟩ c
    exact ⟨t, ht, h _⟩
  · intro h
    classical
    let _ := (stepOk W Λ hX u i).fintypeCl
    choose t ht htx using h
    refine ⟨∏ c, t c, ?_, ?_⟩
    · intro hmem
      obtain ⟨c, -, hc'⟩ := (w.isPrime.prod_mem_iff).1 hmem
      exact ht c hc'
    · refine ((stepGSD W Λ u i).mem_intOf_iff _ (BvLat_equivG W u i (Λ i) v) (stepGSD W Λ u i).outSec _).2 fun c => ?_
      have h2 : ∀ F : VV X.K (W.lamTrue u i), t c • F ∈ BvLat W u i v ((stepGSD W Λ u i).outSec.rep c) →
          (∏ c, t c) • F ∈ BvLat W u i v ((stepGSD W Λ u i).outSec.rep c) := by
        intro F hF
        rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ c), mul_comm]
        have e : ((∏ x ∈ Finset.univ.erase c, t x) * t c) • F = (∏ x ∈ Finset.univ.erase c, t x) • (t c • F) := mul_smul _ _ _
        rw [e]
        exact Submodule.smul_mem _ _ hF
      exact h2 _ (htx c)

theorem Val.bw (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K))
    (hval : ∀ w (x : X.K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) (Q : ValCrd W Λ σ₀ u i)
    (Pv : {P // P ∈ Pr.vT u} → Ideal (𝓞 X.E)) (hPv : ∀ v, Pv v = v.1.asIdeal) :
    Val.Bw W Λ hc hX hPr σ₀ hσ u i Pl pw Q Pv := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  obtain rfl : Pv = fun v => v.1.asIdeal := funext hPv
  intro w hw hs v x
  have := hX.nonempty_Tau
  have hT : (Pr.T u : 𝓞 X.K) ∈ (pw w).asIdeal := hw ▸ vl_resChar_mem Pl pw hval w
  have htau : tauOfR hX hPr u (pw w) v = tauOfC (pw w) v.1 := by
    unfold tauOfR
    rw [dif_pos hT]
    rfl
  rw [vl_mem_span_intW_iff Pl pw hval w (stepBv W Λ u i v) x, mem_localization_stepLattice_iff W Λ hX u i (pw w) v x]
  refine forall_congr' fun c => ?_
  refine (vb_mem_locP_BvLat_iff W hX hPr σ₀ Pl pw hval u i (W.lamN u i) (vl_natW_lamTrue W u i) w hw hs v
    ((stepGSD W Λ u i).outSec.rep c)
    ((x : (stepGSD W Λ u i).D → (stepGSD W Λ u i).V) ((stepGSD W Λ u i).outSec.rep c))).trans ?_
  have hd : dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L =
      ((stepGSD W Λ u i).outSec.rep c).1.Lsh := rlc_span_dualSet hc (R.N i) _
  constructor
  · intro h B B' hB hB'
    have hB1 : IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L : Set (Fin (R.N i) → X.E)) B := hB
    have hB2 : IsLocBasis (Pr.T u) ((((stepGSD W Λ u i).outSec.rep c).1.L ⊔ v.1.asIdeal •
        dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set (Fin (R.N i) → X.E)) B' := hB'
    rw [hd] at hB1 hB2
    obtain ⟨P, hP, he⟩ := h B B' hB1 hB2
    refine ⟨P, hP, fun z => ?_⟩
    rw [htau]
    exact congrFun he z
  · intro h B B' hB hB'
    have hB1 : IsLocBasis (Pr.T u) (dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E)
        ((stepGSD W Λ u i).outSec.rep c).1.L : Set (Fin (R.N i) → X.E)) B := by
      rw [hd]; exact hB
    have hB2 : IsLocBasis (Pr.T u) ((((stepGSD W Λ u i).outSec.rep c).1.L ⊔ v.1.asIdeal •
        dualL (hc.sig : X.E →+* X.E) (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) X.E) ((stepGSD W Λ u i).outSec.rep c).1.L :
        Submodule (𝓞 X.E) (Fin (R.N i) → X.E)) : Set (Fin (R.N i) → X.E)) B' := by
      rw [hd]; exact hB'
    obtain ⟨P, hP, he⟩ := h B B' hB1 hB2
    rw [htau] at he
    exact ⟨P, hP, funext he⟩

end Gen

end Formalism.L2.Col
end
end

