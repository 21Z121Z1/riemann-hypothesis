import Formalism.LocalToGlobal.Columns.Bundle0030
import Formalism.LocalToGlobal.Columns.Bundle0031
import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.TiedBack
import Formalism.LocalToGlobal.Columns.TiedTilA
import Formalism.LocalToGlobal.Columns.Bundle0032
import Formalism.LocalToGlobal.Columns.TwQLevU

-- bundled from Formalism.LocalToGlobal.Columns.HermOwed
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

structure AtTOwed (hS : SpStd d.toColBase) (hH : HostHyp d) where
  disc : ∀ u, AtTDisc (d.colRec a) u
  moves : ∀ u, AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)
  xp : ∀ u, AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)

def hermAtT (hS : SpStd d.toColBase) (hH : HostHyp d) (O : AtTOwed a hS hH) (u : d.what₂.Word) :
    CH.AtT (d.colRec a) u (tieEV d.sp.cm d.hX d.hPr u) (fun v => tieFv d.sp.cm d.hX d.hPr u v) :=
  atTOf (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) (fun v => tieFv d.sp.cm d.hX d.hPr u v)
    (fun v x => tieFv_mk d.sp.cm d.hX d.hPr u v x) (th_seen a hH u) (O.disc u) (O.moves u) (O.xp u)

section Asm

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
  (O : AtTOwed a hS hH)

theorem cofTied : CH.CofTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  intro u
  show (d.piT d.u₀ : d.host.E) / (d.piT u : d.host.E) * (d.piT u : d.host.E) = (d.piT d.u₀ : d.host.E)
  exact div_mul_cancel₀ _ (basePi_of_ok d.hX d.hPr u).coe_ne_zero

theorem baseTied : CH.BaseTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  intro u pb hpb
  have hpb' : algebraMap (𝓞 d.X.E) d.X.E pb = star (algebraMap (𝓞 d.X.E) d.X.E (d.Pr.piT u)) := by
    rw [att_star_eq]
    exact hpb
  refine ⟨?_, fun i h1 hm => ?_⟩
  · rw [coordLattice_selfDual_zero hS]
    exact levPack_base d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) _ _ _ _ (hK u 0) (hCrd0 hS u) pb hpb'
  · rw [coordLattice_selfDual_eq_std hS i hm]
    exact levPack_base d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) _ _ _ _ (hK u i) (hCrd hS u i hm) pb hpb'

structure HermOwed where
  levelZeroCompatibility : CH.Lev0Tied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  ad : CH.AdTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  piG : CH.PiGConst (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) levelZeroCompatibility
  stabMap : CH.StabMapTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)
  fvI : CH.FvStepTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O)

def colsHerm (W : HermOwed a hS hH hP hK S hI O) : CH.ColsHerm (d.colRec a) where
  base := hermCols a hS hP hK S hI
  atT := hermAtT a hS hH O
  levelZeroCompatibility := W.levelZeroCompatibility
  ad := W.ad
  cof := cofTied a hS hH hP hK S hI O
  piG := W.piG
  stabMap := W.stabMap
  fvI := W.fvI
  std := stdTied a hS
  baseL := baseTied a hS hH hP hK S hI O

end Asm

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedAll
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d)

set_option maxHeartbeats 1000000 in

structure FormsOwed (u : d.what₂.Word) where
  gl : GLoc d.host.F d.host.E (CF.sigD (d.colRec a)) d.host.g
  gl_K : ∀ i, (gl.piG i : d.host.E) ∈ d.host.K
  glev : ∀ i hi, GLev (classAgreement a hS hH hP u i hi).lev gl (aOf d.R i) d.R.t i (skipOf d.R i) (fcOf d.R i) (decide (i = d.R.m))
  fMe : ∀ i hi v, (classAgreement a hS hH hP u i hi).lev.fM ((atTTied a hH u).eV v).1 ((atTTied a hH u).eV v).2 ≃+
    ((d.colRec a).mem u).A.Fv v
  fv : ∀ i hi, CF.FvTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (fMe i hi)
  upN : ∀ i hi, CF.UpNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (valuationAgreementConcrete a hS hH hP u i hi)
  dnN : ∀ i hi, CF.DnNatTie (levelAgreement a hS hH u i hi) (classAgreement a hS hH hP u i hi) (valuationAgreementConcrete a hS hH hP u i hi)
  clsP : CF.ClsPTied (D := d.colRec a) u
  valP : CF.ValPTied (D := d.colRec a) u clsP
  normP : CF.NormPTie valP
  glevP : GLev clsP.lev gl d.R.r d.R.t d.R.m (d.R.N d.R.m) (fcOf d.R d.R.m) false
  til : CF.TilTied (D := d.colRec a) u (atTTied a hH u) clsP (levelAgreement a hS hH u d.R.m le_rfl)
  tilLat : CF.TilBaseLat til (classAgreement a hS hH hP u d.R.m le_rfl)
  tilFv : CF.TilBaseFv til (classAgreement a hS hH hP u d.R.m le_rfl) (fMe d.R.m le_rfl)
  tilAd : CF.TilAd til (classAgreement a hS hH hP u d.R.m le_rfl)
  frExt : CF.FrExt til.z0 (glev d.R.m le_rfl) glevP
  eWz : ((d.colRec a).mem u).P.Wz ≃ₗ[ℂ] (((d.colRec a).fm u).clsP → ((d.colRec a).mem u).C.Y d.R.m → ℂ)
  evz : CF.EvzTie tilAd (valuationAgreementConcrete a hS hH hP u d.R.m le_rfl) eWz
  jM : ((d.colRec a).mem u).P.Mt →ₛₗ[starRingEnd ℂ] ((d.colRec a).mem u).P.Wrow
  per : CF.PerTie (D := d.colRec a) u jM

variable {a hS hH hP}

set_option maxHeartbeats 1000000 in

def formsTied {u : d.what₂.Word} (O : FormsOwed a hS hH hP u) : CF.FormsTied (d.colRec a) u where
  atT := atTTied a hH u
  cls := fun i hi => classAgreement a hS hH hP u i hi
  val := fun i hi => valuationAgreementConcrete a hS hH hP u i hi
  gl := O.gl
  gl_K := O.gl_K
  glev := O.glev
  lv := fun i hi => levelAgreement a hS hH u i hi
  fMe := O.fMe
  fv := O.fv
  upN := O.upN
  dnN := O.dnN
  norm := fun i hi => stepNormTie a hS hH hP u i hi
  bw := fun i hi => stepBwTie a hS hH hP u i hi
  clsP := O.clsP
  valP := O.valP
  normP := O.normP
  glevP := O.glevP
  til := O.til
  tilLat := O.tilLat
  tilFv := O.tilFv
  tilAd := O.tilAd
  frExt := O.frExt
  eWz := O.eWz
  evz := O.evz
  jM := O.jM
  per := O.per
  DGam := rfl

variable (a hS hH hP)

structure ColsOwed where
  forms : ∀ u : d.what₂.Word, FormsOwed a hS hH hP u
  herm : CH.ColsHerm (d.colRec a)
  joint : ∀ u, CF.Joint herm u (formsTied (forms u))
  gl_const : ∀ u u', (forms u).gl = (forms u').gl
  chi : CharacterCompatible (forms d.u₀).gl d.R.m
  fr_const : ∀ u u' (i : ℕ) (hi : i ≤ d.R.m), i < d.R.m → ((forms u).glev i hi).fr = ((forms u').glev i hi).fr
  frP_const : ∀ u u', (forms u).glevP.fr = (forms u').glevP.fr

variable {a hS hH hP}

def colsTied (O : ColsOwed a hS hH hP) : CF.ColsTied (d.colRec a) where
  herm := O.herm
  forms := fun u => formsTied (O.forms u)
  joint := O.joint
  gl_const := O.gl_const
  chi := O.chi
  fr_const := O.fr_const
  frP_const := O.frP_const

def colsTiedD {D : D7} (h : D.colRec = d.colRec a) (O : ColsOwed a hS hH hP) : Formalism.L2.Forms.ColsTied D :=
  columnsAgreement_of_eq h (colsTied O)

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedTilB
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem til_tmv_padL_cs (n : ℕ) {R : Type} [CommRing R] (φ : E →+* R) (a b : Fin n) :
    ((LinearMap.toMatrix' (padL E n (n + 1))).map φ) a.castSucc b = if a = b then 1 else 0 := by
  rw [Matrix.map_apply, LinearMap.toMatrix'_apply, padL_apply, dif_pos (by simp), Pi.single_apply]
  have e : (⟨(a.castSucc : ℕ), by simp⟩ : Fin n) = a := Fin.ext rfl
  rw [e]
  split_ifs
  · exact map_one φ
  · exact map_zero φ

theorem til_tmv_padL_last (n : ℕ) {R : Type} [CommRing R] (φ : E →+* R) (b : Fin n) :
    ((LinearMap.toMatrix' (padL E n (n + 1))).map φ) (Fin.last n) b = 0 := by
  rw [Matrix.map_apply, LinearMap.toMatrix'_apply, padL_apply, dif_neg (by simp), map_zero]

theorem til_tmv_move (hc : CMData F E) {N n : ℕ} (hN : N = n + 1) [NeZero N] [NeZero n] (ST SG : Finset (Pl E))
    (H : Subgroup (GLG E N SG)) (c₀ : DiaG E ST) {pi : 𝓞 E} (h0 : pi ≠ 0)
    (hcP : ∀ P : ST, ((c₀ P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (cO E pi))
    (hw : ∀ w : SG, pi - 1 ∈ w.1.asIdeal) (hS' : DecoPtSurj hc n (∅ : Finset (Pl E)) SG) (hS : DecoPtSurj hc N ST SG)
    (d' : DecoSet E n ∅ SG) (e : DecoSet E N ST SG) (a : UF E N × H)
    (ha : a • e = (DecoSet.tilH (ST := ST) hN pi d').res (Finset.Subset.refl _)) :
    ∃ κ : levU hc N ST SG H, levRed hc N ST SG H κ = a.2 ∧
      ∀ g : GL (Fin N) (E ⊗[F] Formalism.L2.Herm.Af F),
        g.1 * (LinearMap.toMatrix' (padL E n N)).map (iA F E) =
          (LinearMap.toMatrix' (padL E n N)).map (iA F E) * (ptOfD hc n ∅ SG 1 d').1.1 →
        g.1 *ᵥ (fun j => iA F E ((Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi) : Fin N → E) j)) =
          (fun j => iA F E ((Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi) : Fin N → E) j)) →
        bc (iA F E) ((ratEquiv hc N).symm a.1).1 * (ptOfD hc N ST SG c₀ e).1 = g * κ.1 := by
  subst hN
  have hy' : decoOf (∅ : Finset (Pl E)) SG (ptOfD hc n ∅ SG 1 d').1 = d' := by
    unfold ptOfD
    rw [decoOf_ptOf hc n ∅ SG hS', inv_one, DecoSet.dia_one]
  have hy : decoOf ST SG (ptOfD hc (n + 1) ST SG c₀ e).1 = e.dia c₀⁻¹ := by
    unfold ptOfD
    rw [decoOf_ptOf hc (n + 1) ST SG hS]
  have ha' : a • e = DecoSet.til (ST := ST) pi d' := ha
  have h1 := til_tmv_decoOfD ST SG hc (ptOfD hc n ∅ SG 1 d').2 c₀ hcP hw
  rw [hy', ← ha'] at h1
  have h2 : decoOf ST SG (padA F E n (ptOfD hc n ∅ SG 1 d').1) = a • decoOf ST SG (ptOfD hc (n + 1) ST SG c₀ e).1 := by
    rw [hy]
    have h3 := congrArg (fun t => DecoSet.dia c₀⁻¹ t) h1
    have h4 : (decoOfD (n + 1) ST SG c₀ (padA F E n (ptOfD hc n ∅ SG 1 d').1)).dia c₀⁻¹ =
        decoOf ST SG (padA F E n (ptOfD hc n ∅ SG 1 d').1) := DecoSet.dia_inv_dia c₀ _
    exact h4.symm.trans h3
  obtain ⟨γ, k, hγ, hk, hx⟩ := rlc_rel_of_orbit hc (n + 1) ST SG H
    (x := ⟨padA F E n (ptOfD hc n ∅ SG 1 d').1, padA_mem_UAd hc (ptOfD hc n ∅ SG 1 d').2⟩) (y := ptOfD hc (n + 1) ST SG c₀ e) a h2
  refine ⟨k, hk, fun g hg1 hg2 => ?_⟩
  have hγ' : (ratEquiv hc (n + 1)).symm a.1 = γ := (MulEquiv.symm_apply_eq _).2 hγ.symm
  have hp : algebraMap (𝓞 E) E pi ≠ 0 := by
    intro hz
    exact h0 (RingOfIntegers.ext (by simpa using hz))
  have hg : g = padA F E n (ptOfD hc n ∅ SG 1 d').1 := by
    apply Units.ext
    refine til_tmv_eq_padM _ (til_tmv_padL_cs n (iA F E)) (til_tmv_padL_last n (iA F E)) _ ?_ ?_ _ _ hg1 hg2
    · intro j
      rw [til_tmv_lastIdx, Pi.single_eq_of_ne (Fin.castSucc_ne_last j), map_zero]
    · rw [til_tmv_lastIdx, Pi.single_eq_same]
      exact hp.isUnit.map (iA F E)
  rw [hγ', hg]
  have hx' : padA F E n (ptOfD hc n ∅ SG 1 d').1 = bc (iA F E) (γ : GL (Fin (n + 1)) E) * (ptOfD hc (n + 1) ST SG c₀ e).1 * (k.1)⁻¹ := hx
  rw [hx', inv_mul_cancel_right]

end Gen

section Pr

variable {X : Fields} {Pr : Primes X}

theorem til_tmv_piT_sub_one (hPr : Pr.Ok) (u : Pr.Word) (w : Pr.vGs) : Pr.piT u - 1 ∈ w.1.asIdeal := by
  have hgg : ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := by
    obtain ⟨i, hi⟩ := exists_g_mem hPr w
    push_cast
    apply Ideal.mul_mem_left
    rw [sq]
    apply Ideal.mul_mem_left
    fin_cases i
    · exact Ideal.mul_mem_right _ _ hi
    · exact Ideal.mul_mem_left _ _ hi
  exact Ideal.mem_of_dvd _ (hPr.piT_cong u) hgg

theorem til_tmv_diaT (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    ((diaT u P : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) := by
  have := P.1.isMaximal
  let _ := Ideal.Quotient.field P.1.asIdeal
  have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (X.conjO (Pr.piT u))) :=
    (mk_ne_zero (conj_piT_notMem hPr u P)).isUnit
  unfold diaT
  rw [dif_pos hu]
  rfl

theorem til_tmv_colDia (hPr : Pr.Ok) (R : Ranks) (u : Pr.Word) (P : Pr.vT u) :
    ((colDia R u R.m P : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) := by
  unfold colDia
  rw [if_neg (lt_irrefl _)]
  exact til_tmv_diaT hPr u P

end Pr

section Rec

variable {d : ColDat} (a : ColArgs d)

set_option maxHeartbeats 1000000 in

theorem til_tmv_rec (hS : SpStd d.toColBase) (hP : PtSurjP d) (hQ : PtSurj d) (u : d.what₂.Word) (c : PCl d) :
    ∃ κ : levU d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp,
    levRed d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp κ = (d.tilMv u c).2 ∧
    ∀ g : GL (Fin (d.R.N d.R.m)) (d.host.E ⊗[d.host.F] FiniteAdeleRing (𝓞 d.host.F) d.host.F),
      CF.IsExt (d.colRec a) (d.z0 u) (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F))
        (ptOfD d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs 1 (d.reprP c)).1.1 g.1 →
      bc (inclE (F := d.host.F) (FiniteAdeleRing (𝓞 d.host.F) d.host.F)) (d.tilGa u c).1 *
        (ptOfD d.sp.cm (d.R.N d.R.m) (d.Pr.vT u) d.Pr.vGs (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m)
          (d.repr u d.R.m (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c))).1 = g * κ.1 := by
  have h0 : d.Pr.piT u ≠ 0 := fun h => piT_coe_ne_zero (d := d) u (by
    show ((d.Pr.piT u : 𝓞 d.X.E) : d.X.E) = 0
    rw [h]; rfl)
  obtain ⟨κ, h1, h2⟩ := til_tmv_move (F := d.X.F) (E := d.X.E) d.sp.cm (N_m_succ d.R) (d.Pr.vT u) d.Pr.vGs (d.lev d.R.m).grp
    (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) h0 (til_tmv_colDia d.hPr d.R u) (til_tmv_piT_sub_one d.hPr u) hP (hQ u d.R.m)
    (d.reprP c) (d.repr u d.R.m (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c)) (d.tilMv u c) (tilMv_smul u c)
  refine ⟨κ, h1, fun g hg => h2 g ?_ hg.2⟩
  have h3 := hg.1
  unfold CF.iXm at h3
  rw [iXc_eq a hS] at h3
  exact h3

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedUpDnB
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG
open Formalism.L2.DIV (Pl)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

theorem tud_lat_move (γ : URat hc n) (g₀ : UF E n × H) (hγ : ratHom hc n γ = g₀.1) (d' d₁ : DecoSet E n ST SG)
    (hg₀ : g₀ • d' = d₁) (P : ST) :
    Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.L = d₁.1.L ∧
      Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.Lsh = d₁.1.Lsh ∧
      ∀ y, d'.1.f P y = d₁.1.f P (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) := by
  subst hg₀
  have hm : ∀ L : Submodule (𝓞 E) (Sp E n), Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) L =
      gmap ((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n) L := by
    intro L
    unfold Formalism.L2.Forms.mulLat gmap
    congr 1
    apply LinearMap.ext
    intro y
    show _ = ((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n) y
    rw [← hγ]
    exact (rlc_ratHom_apply hc n γ y).symm
  refine ⟨by rw [hm, rlc_smul_val, Deco.L_act], by rw [hm, rlc_smul_val, Deco.Lsh_act _ g₀.1.2], fun y => ?_⟩
  show d'.1.f P y = d'.1.f P (((g₀.1 : UF E n) : Sp E n ≃ₗ[E] Sp E n).symm (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y))
  rw [← hγ, ← rlc_ratHom_apply, LinearEquiv.symm_apply_apply]

omit [Algebra F E] in
theorem tud_f_rep (d : DecoSet E n ST SG) (P : ST) {x : d.lv P} (hx : d.fv P x = 1) : d.1.f P (modP.rep x) = 1 := by
  rw [← d.fv_mk P ⟨modP.rep x, modP.rep_mem x⟩, modP.mk_rep, hx]

theorem tud_up_core (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) {v : HeightOneSpectrum (𝓞 F)} (d d' : DecoSet E n ST SG)
    (P : ST) (hov : IsOver v P.1) (hP : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
    {a : 𝓞 E} (ha : SepElt ST a) (x : d.lv P) (hx : d.fv P x = 1) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d.upL P q x) :
    ∃ (γ : URat hc n) (η : UAd hc n) (κ : levU hc n ST SG H), ratHom hc n γ = g₀.1 ∧ levRed hc n ST SG H κ = g₀.2 ∧
      (∀ v', v' ≠ v → bc (prV (E := E) v') (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
      bc (iA F E) (γ : GL (Fin n) E) * (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (ptOfD hc n ST SG c₀ d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * η * κ ∧
      localization₂ P.1.asIdeal (Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.L) = localization₂ P.1.asIdeal d.1.Lsh ∧
      (∀ {w : Sp E n} {t : 𝓞 E}, t ∉ P.1.asIdeal → w ∈ d.1.Lsh → modP.rep x - t • w ∈ P.1.asIdeal • d.1.N →
        localization₂ P.1.asIdeal (Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.Lsh) =
          localization₂ P.1.asIdeal (d.1.Lsh ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • w})) ∧
      ∀ y ∈ d'.1.Lsh, d'.1.f P y = d.1.f P (q • (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y)) := by
  have hfr := tud_f_rep n ST SG d P hx
  have hd₁ : (d.upL P q x).1 = d.1.up P q (modP.rep x) := d.up_val P hP hq hq2 (modP.rep_mem x) hfr
  have hSO := tud_sameOff_up hc d P hP hq hq2 hov (modP.rep_mem x) hfr
  obtain ⟨γ, η, κ, hγ, hκ, hη, e⟩ := updn_move hc n ST SG H hS c₀ v d (d.upL P q x) d' hSO g₀ hg₀
  obtain ⟨hL, hLs, hf⟩ := tud_lat_move hc n ST SG H γ g₀ hγ d' _ hg₀ P
  refine ⟨γ, η, κ, hγ, hκ, hη, e, ?_, ?_, ?_⟩
  · rw [hL, tud_locP_L ha, DecoSet.locP_LshKer_up hP hq hq2 ha (d.upL_mem P hP hq hq2 hx) P]
  · intro w t ht hw hrw
    rw [hLs, (d.upL P q x).2.locP_Lsh ha P, show (d.upL P q x).1.N = upN P.1.asIdeal d.1.N (modP.rep x) from
      congrArg Deco.N hd₁, localizationAt_upN d.2.lat d.2.uni P.1 hP.ne (modP.rep_mem x)]
    exact localizationAt_upA hq hq2 d.2.N_le_Lsh (by rw [← d.2.locP_Lsh ha P]; exact le_locP _ _) hw ht hrw
  · intro y hy
    have hy1 : ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y ∈ (d.upL P q x).1.Lsh := by
      rw [← hLs]; exact Submodule.mem_map_of_mem hy
    have hy2 := (d.upL P q x).2.Lsh_le_at ha P hy1
    rw [hf y, hd₁, Deco.up_f, if_pos]
    rw [hd₁] at hy2
    exact hy2

theorem tud_dn_core (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) {v : HeightOneSpectrum (𝓞 F)} (d d' : DecoSet E n ST SG)
    (P : ST) (hov : IsOver v P.1) (hP : MoveHyp ST SG P) {a : 𝓞 E} (ha : SepElt ST a)
    (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (d.lk P)) (hg : g ≠ 0) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d.dnL P g) :
    ∃ (γ : URat hc n) (η : UAd hc n) (κ : levU hc n ST SG H), ratHom hc n γ = g₀.1 ∧ levRed hc n ST SG H κ = g₀.2 ∧
      (∀ v', v' ≠ v → bc (prV (E := E) v') (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
      bc (iA F E) (γ : GL (Fin n) E) * (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (ptOfD hc n ST SG c₀ d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * η * κ ∧
      localization₂ P.1.asIdeal (Formalism.L2.Forms.mulLat ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) d'.1.Lsh) = localization₂ P.1.asIdeal d.1.L ∧
      ∀ y, d'.1.f P y = modP.ext P.1 (d.1.kerAt P) g (((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y) := by
  classical
  have hd₁ := d.dnL_val P hP hg
  have hSO := tud_sameOff_dn hc d P hP hg hov
  obtain ⟨γ, η, κ, hγ, hκ, hη, e⟩ := updn_move hc n ST SG H hS c₀ v d (d.dnL P g) d' hSO g₀ hg₀
  obtain ⟨-, hLs, hf⟩ := tud_lat_move hc n ST SG H γ g₀ hγ d' _ hg₀ P
  refine ⟨γ, η, κ, hγ, hκ, hη, e, ?_, fun y => ?_⟩
  · rw [hLs, (d.dnL P g).2.locP_Lsh ha P, show (d.dnL P g).1.N = d.1.dnN P from congrArg Deco.N hd₁,
      (d.2.dnN_spec P hP.ne).2.2.2, ← d.2.locP_LshKer_self ha P, tud_locP_L ha]
  · rw [hf y, hd₁]
    show Function.update d.1.f P _ P _ = _
    rw [Function.update_self]

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQSpP
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section SpP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)
  (P : Pl E) (ϖ : 𝓞 E) (hϖ : ϖ ∈ P.asIdeal) (hcϖ : cO E ϖ ∉ P.asIdeal)
  (s : Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P) (ϖ : E))

abbrev qbPhi : E →+* (underPl F P).adicCompletion F :=
  (RingHom.fst _ _).comp (s.φ.toRingHom.comp (inclE (F := F) ((underPl F P).adicCompletion F)))

theorem phi_integral_valuation_le_one (r : 𝓞 E) : Valued.v (qbPhi hc P ϖ s (algebraMap (𝓞 E) E r)) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((s.int _).1 (Formalism.MainNotions.Gaps.LG.sc_left_mem _ r)).1

theorem qsp_sp_F (x : F) : qbPhi hc P ϖ s (algebraMap F E x) = algebraMap F ((underPl F P).adicCompletion F) x := by
  show (s.φ (algebraMap F E x ⊗ₜ[F] (1 : (underPl F P).adicCompletion F))).1 = _
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, s.alg]

include hϖ hcϖ in
set_option maxHeartbeats 2000000 in

theorem qsp_sp_P (r : 𝓞 E) : Valued.v (qbPhi hc P ϖ s (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal := by
  have hval : Valued.v (gloPhi (underPl F P) s.φ (inclE (F := F) ((underPl F P).adicCompletion F) (algebraMap (𝓞 E) E ϖ))) < 1 := s.ori
  have hker := glk_ker hc (underPl F P) s.φ s.alg P (qsp_isOver P) ϖ hcϖ hval
  have key : ∀ a : 𝓞 E, a ∈ P.asIdeal → Valued.v (qbPhi hc P ϖ s (algebraMap (𝓞 E) E a)) < 1 := fun a ha => by
    have h1 := hker a ha
    rw [gloRho_oToS] at h1
    have h2 := glk_val_lt (underPl F P) _ h1
    exact h2
  refine ⟨fun h => ?_, key r⟩
  by_contra hr
  obtain ⟨y, i, hi, e⟩ := P.isMaximal.exists_inv hr
  have h1 : qbPhi hc P ϖ s (algebraMap (𝓞 E) E y) * qbPhi hc P ϖ s (algebraMap (𝓞 E) E r) +
      qbPhi hc P ϖ s (algebraMap (𝓞 E) E i) = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_add, e, map_one, map_one]
  have h2 : Valued.v (qbPhi hc P ϖ s (algebraMap (𝓞 E) E y) * qbPhi hc P ϖ s (algebraMap (𝓞 E) E r)) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (phi_integral_valuation_le_one hc P ϖ s y)) h
  have h3 := Valuation.map_add_lt Valued.v h2 (key i hi)
  rw [h1, map_one] at h3
  exact lt_irrefl _ h3

end SpP

end Formalism.L2.Col
end
end

