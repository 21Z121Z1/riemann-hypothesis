import Formalism.LocalToGlobal.Columns.Bundle0033
import Formalism.LocalToGlobal.Columns.MtHeckeLoc
import Formalism.LocalToGlobal.Columns.Bundle0034
import Formalism.LocalToGlobal.Columns.Bundle0029
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

-- bundled from Formalism.LocalToGlobal.Columns.CharactersLevelZeroAgree
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem th_reGL_id {n : ℕ} (R : Type) [CommRing R] :
    (Formalism.L2.Forms.reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id (GL (Fin n) R) :=
  MonoidHom.ext fun x => Formalism.L2.Forms.reGL_rfl R x

theorem th_sameCar_refl {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {cls : Type} {stab : cls → Type} (Lb : Submodule (𝓞 E) (Fin n → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (y : cls → GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (st : ∀ c, stab c → GL (Fin n) E) :
    Formalism.L2.Forms.SameCar (rfl : n = n) Lb Lb Uloc Uloc U U y y st st where
  Lb_eq := (Formalism.L2.Forms.reL_rfl Lb).symm
  Uloc_eq := fun v => by rw [th_reGL_id, Subgroup.map_id]
  U_eq := by rw [th_reGL_id, Subgroup.map_id]
  y_eq := fun c => (Formalism.L2.Forms.reGL_rfl _ (y c)).symm
  st_eq := fun c s => (Formalism.L2.Forms.reGL_rfl _ (st c s)).symm

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem levPack_sameCar (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (Q : StepCrd Pr σ₀ n fun c => (s c).1.L) :
    Formalism.L2.Forms.SameCar H.hn (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Lb
      (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Uloc (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Uloc
      (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.U (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.U
      (fun c => ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.y c).1) (fun c => ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).y c).1)
      (fun c t => ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.stabI c t).1)
      (fun c t => ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).stabI c t).1) := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_sameCar_refl _ _ _ _ _

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)

theorem characters_level_zero_agree (u : d.what₂.Word) :
    Formalism.L2.Forms.SameCar (Formalism.L2.Forms.rank_eq_first_level d.R) ((hermCols a hS hP hK S hI).lev0 u).Lb (classAgreement a hS hH hP u 0 (Nat.zero_le _)).lev.Lb
      ((hermCols a hS hP hK S hI).lev0 u).Uloc (classAgreement a hS hH hP u 0 (Nat.zero_le _)).lev.Uloc
      ((hermCols a hS hP hK S hI).lev0 u).U (classAgreement a hS hH hP u 0 (Nat.zero_le _)).lev.U
      (fun c => (((hermCols a hS hP hK S hI).lev0 u).y c).1) (fun c => ((classAgreement a hS hH hP u 0 (Nat.zero_le _)).y c).1)
      (fun c t => (((hermCols a hS hP hK S hI).lev0 u).stabI c t).1)
      (fun c t => ((classAgreement a hS hH hP u 0 (Nat.zero_le _)).stabI c t).1) :=
  levPack_sameCar d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) _ _ _ _ (hK u 0) (hCrd0 hS u) (stepCrd a hS hH u 0 (Nat.zero_le _))

theorem th_carI (u : d.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ d.R.m) :
    Formalism.L2.Forms.SameCar (CF.rankN (d.colRec a) i hm) ((hermCols a hS hP hK S hI).lev u i h1 hm).Lb (classAgreement a hS hH hP u i hm).lev.Lb
      ((hermCols a hS hP hK S hI).lev u i h1 hm).Uloc (classAgreement a hS hH hP u i hm).lev.Uloc
      ((hermCols a hS hP hK S hI).lev u i h1 hm).U (classAgreement a hS hH hP u i hm).lev.U
      (fun c => (((hermCols a hS hP hK S hI).cls u i h1 hm).y c).1) (fun c => ((classAgreement a hS hH hP u i hm).y c).1)
      (fun c t => (((hermCols a hS hP hK S hI).cls u i h1 hm).stabI c t).1)
      (fun c t => ((classAgreement a hS hH hP u i hm).stabI c t).1) :=
  levPack_sameCar d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) _ _ _ _ (hK u i) (hCrd hS u i hm) (stepCrd a hS hH u i hm)

end Rec

section Pr

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem th_pr (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) (z' : ↥(CF.Ld D u i hi c))
    (h : z'.1 = CF.crdN D i hi z.1) : (P i hi).pr v c z' = hxPr A P i v c z := by
  rw [hxPr_eq A P i hi]
  congr 1
  exact Subtype.ext h

theorem th_prk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c))
    (z' : ↥(CF.Lk A i hi v c)) (h : z'.1 = CF.crdN D i hi z.1) : (P i hi).prk v c z' = hxPrk A P i v c z := by
  rw [hxPrk_eq A P i hi]
  congr 1
  exact Subtype.ext h

end Pr

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MtHeckeSum
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Sum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhs_cosets_finite (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) : (mhlCosets hc (n := n) v U k).Finite := by
  have hB := mhl_split_bij' hc U k ST SG hov hST hSG hsp hk 1
  refine Set.Finite.of_finite_image ?_ hB.injOn
  rw [hB.image_eq]
  exact DecoSet.heckeSet_finite (conjPrime₂ Pb).ne_bot (conjIdeal_ne_bot (conjPrime₂ Pb).ne_bot) k _

theorem mhs_exists_reps (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) :
    ∃ R : Finset (UAd hc n), Set.BijOn (fun η : UAd hc n => (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v)) R
      (mhlCosets hc v U k) := by
  classical
  have hfin := mhs_cosets_finite hc U k ST SG hov hST hSG hsp hk
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_, ?_⟩
  · intro η hη
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη
    obtain ⟨c, hc', rfl⟩ := hη
    show (QuotientGroup.mk c.out : UAd hc n ⧸ mhlKv hc n v) ∈ mhlCosets hc v U k
    rw [QuotientGroup.out_eq']
    exact hc'
  · intro η hη η' hη' h
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη hη'
    obtain ⟨c, -, rfl⟩ := hη
    obtain ⟨c', -, rfl⟩ := hη'
    have h' : c = c' := (QuotientGroup.out_eq' c).symm.trans (h.trans (QuotientGroup.out_eq' c'))
    rw [h']
  · intro c hc'
    refine ⟨c.out, ?_, QuotientGroup.out_eq' c⟩
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset]
    exact ⟨c, hc', rfl⟩

theorem mhs_decoOf_out (ST SG : Finset (Pl E)) (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q)
    (x η : UAd hc n) :
    decoOf ST SG ((x * (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v).out : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = decoOf ST SG ((x * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul (mhlKv hc n v) η
  rw [e, ← mul_assoc, Subgroup.coe_mul]
  exact decoOf_mul_mhlKv ST SG hST hSG _ h.2

end Sum

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedTilC
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

theorem tilMove (hS : SpStd d.toColBase) (hP : PtSurjP d) (hQ : PtSurj d) (u : d.what₂.Word) : TilMove a u :=
  fun c => til_tmv_rec a hS hP hQ u c

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedXpB
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))
  (h : BasePi ST π)

theorem tb_psi_incl {P : Pl E} (hov : IsOver v P) (t : baseDualV hc n ST v) (x : Fin n → E) (r : 𝓞 E)
    (ht : t.1 = fun a => inclE (F := F) (v.adicCompletion F) (x a))
    (hr : algebraMap (𝓞 E) E r = star (algebraMap (𝓞 E) E π) * x (lastIdx n)) :
    rll_psi hc n v h P t = Ideal.Quotient.mk P.asIdeal r := by
  have hm : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r) * ((1 : Formalism.BasicNotions.intV E v) : E ⊗[F] v.adicCompletion F) ∈
      Formalism.BasicNotions.intV E v := mul_mem (rll_incl_int v r) (one_mem _)
  have h1 := rll_rho_incl_mul v P r 1 hm
  rw [rll_rho_one v hov, mul_one] at h1
  rw [← h1]
  show rll_rho v P _ = rll_rho v P _
  congr 1
  apply Subtype.ext
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π)) * t.1 (lastIdx n) =
    inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r) * ((1 : Formalism.BasicNotions.intV E v) : E ⊗[F] v.adicCompletion F)
  rw [ht, ← map_mul, ← hr]
  exact (mul_one _).symm

end Fun

section GenQ

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

variable (c₀ : DiaG X.E (Pr.vT u))

theorem hermForm_lastVector_apply (x : Fin n → X.E) :
    hform (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E)
      (Pi.single (lastIdx n) (algebraMap (𝓞 X.E) X.E (Pr.piT u))) x =
      star (algebraMap (𝓞 X.E) X.E (Pr.piT u)) * x (lastIdx n) := by
  refine (rf_hform_one (X := X) _ _).trans ?_
  rw [hStd_apply, Finset.sum_eq_single (lastIdx n)]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tb_fvMe_fLoc (P : Pr.vT u) (hc₀ : (c₀ P).1 = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)))
    (t : baseDualV hc n (Pr.vT u) (tieEV hc hX hPr u P).1) (x : Fin n → X.E) (r : 𝓞 X.E)
    (ht : t.1 = fun a => inclE (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (x a))
    (hr : algebraMap (𝓞 X.E) X.E r = star (algebraMap (𝓞 X.E) X.E (Pr.piT u)) * x (lastIdx n)) :
    fvMe hc hX hPr u c₀ P (fLoc hc n (Pr.vT u) (tieEV hc hX hPr u P).1 t) = Ideal.Quotient.mk P.1.asIdeal r := by
  have h1 : Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) * Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) = 1 := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk P.1.asIdeal), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (tieInv_spec hPr u P)
  have ha : (c₀ P).1 * Ideal.Quotient.mk P.1.asIdeal (tieInv hPr u P) = 1 := (congrArg (· * _) hc₀).trans h1
  have hp := tb_psi_incl hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) (tieEV_over hc hX hPr u P) t x r ht hr
  refine (fvMeL_fLoc hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) P.2 (tieEV_over hc hX hPr u P)
    ((basePi_of_ok hX hPr u).over_unique hc P.2 (tieEV_over hc hX hPr u P)) _ _ (fv_unit hPr u c₀ P) t).trans ?_
  exact ((congrArg (· * rll_psi hc n (tieEV hc hX hPr u P).1 (basePi_of_ok hX hPr u) P.1 t) ha).trans (one_mul _)).trans hp

variable (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
  (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

set_option maxHeartbeats 1000000 in

theorem tb_baseFv (P : Pr.vT u) (hc₀ : (c₀ P).1 = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)))
    (t : latS (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (intV X.E (tieEV hc hX hPr u P).1)
      (Submodule.span (𝓞 X.E) (dualSet (hc.sig : X.E →+* X.E) Q.J (clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.Lb)))
    (x : Fin n → X.E) (r : 𝓞 X.E)
    (ht : t.1 = fun a => inclE (F := X.F) ((tieEV hc hX hPr u P).1.adicCompletion X.F) (x a))
    (hr : algebraMap (𝓞 X.E) X.E r =
      hform (hc.sig : X.E →+* X.E) Q.J (Pi.single (lastIdx n) (algebraMap (𝓞 X.E) X.E (Pr.piT u))) x) :
    tieFMe hc hX hPr σ₀ u Λ c₀ s hS hs Q P
      ((clsG hc hX hPr σ₀ u Λ c₀ s hS hs Q).lev.fT (tieEV hc hX hPr u P).1 (tieEV hc hX hPr u P).2 t) =
        Ideal.Quotient.mk P.1.asIdeal r := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact tb_fvMe_fLoc hc hX hPr u c₀ P hc₀ t x r ht (hr.trans (hermForm_lastVector_apply hc u x))

omit [NeZero n] in

theorem tb_colDia_top (hPr : Pr.Ok) (u : Pr.Word) (R : Ranks) (P : Pr.vT u) :
    (colDia (X := X) (Pr := Pr) R u R.m P).1 = Ideal.Quotient.mk P.1.asIdeal (cO X.E (Pr.piT u)) := by
  have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (X.conjO (Pr.piT u))) := by
    have hmax : P.1.asIdeal.IsMaximal := P.1.isMaximal
    let _ := Ideal.Quotient.field P.1.asIdeal
    exact isUnit_iff_ne_zero.2 fun h0 => conj_piT_notMem hPr u P (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  unfold colDia
  rw [if_neg (lt_irrefl _)]
  unfold diaT
  rw [dif_pos hu]
  rfl

end GenQ

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d)

set_option maxHeartbeats 1000000 in

theorem tilBaseFv (u : d.what₂.Word) :
    CF.TilBaseFv (tildeLatticeAgreement a hS hH hP u) (classAgreement a hS hH hQ u d.R.m le_rfl) (formModuleEquivAtPlace a hS hH hQ u d.R.m le_rfl) :=
  fun v t x r ht hr =>
    tb_baseFv d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
      (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl) v
      (tb_colDia_top d.hPr u d.R v) t x r ht hr

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedXpW
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d)

theorem ufGL_tilMv (u : d.what₂.Word) (c : PCl d) :
    ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1 = (d.tilGa u c).1 := by
  have h := vfi_ufGL_ratHom d.sp.cm (d.R.N d.R.m) (d.tilGa u c)
  have e : ratHom d.sp.cm (d.R.N d.R.m) (d.tilGa u c) = (d.tilMv u c).1 :=
    (ratEquiv d.sp.cm (d.R.N d.R.m)).apply_symm_apply _
  rw [e] at h
  exact h

theorem chi_ka (u : d.what₂.Word) (hM : TilMove a u) (c : PCl d) :
    ((((classAgreement a hS hH hQ u d.R.m le_rfl).lev.chi ((tilAd a hS hH hP hQ u hM).ka c))⁻¹ : ℂˣ) : ℂ) =
      d.σ₀ (((d.lev d.R.m).chr (d.tilMv u c).2 : d.X.Kˣ) : d.X.K) := by
  have h1 := xp_clsG_chi d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) (colDia (X := d.X) (Pr := d.Pr) d.R u d.R.m) (d.repr u d.R.m)
    (hQ u d.R.m) (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.spec c) (stepCrd a hS hH u d.R.m le_rfl)
    ((tilAd a hS hH hP hQ u hM).ka c) (hM c).choose.2
  have h2 : (classAgreement a hS hH hQ u d.R.m le_rfl).lev.chi ((tilAd a hS hH hP hQ u hM).ka c) =
      levTyp ((Units.map d.σ₀.toMonoidHom).comp (d.lev d.R.m).chr) (hM c).choose := h1
  rw [h2, ← map_inv, vfi_typ d.sp.cm d.σ₀ (d.lev d.R.m), inv_inv, (hM c).choose_spec.1]

theorem evz_core (u : d.what₂.Word) (c : PCl d) (s s' : FrS d.X d.σ₀ (d.R.N d.R.m))
    (h : IsTr (atInf (embAt d.σ₀ d.X.emb) (d.tilGa u c).1.1) s' s) :
    frMul d.σ₀ (ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1)⁻¹ s = s' := by
  rw [ufGL_tilMv]
  exact vfi_frMul_of_isTr d.σ₀ _ s s' h

theorem evzTied (u : d.what₂.Word) (hM : TilMove a u)
    (W : CF.ValTied (D := d.colRec a) u (atTTied a hH u).eV d.R.m le_rfl (classAgreement a hS hH hQ u d.R.m le_rfl))
    (hW : ∀ s, (W.eY s).1 = s.1) :
    CF.EvzTie (tilAd a hS hH hP hQ u hM) W (tieEWz a u) := by
  intro φ c s s' hTr
  have hs : frMul d.σ₀ (ufGL d.X.E (d.R.N d.R.m) (d.tilMv u c).1)⁻¹ s = s' := by
    refine evz_core u c s s' fun τ => ?_
    have h := hTr τ
    have e1 := congrFun (hW s) τ
    have e2 := congrFun (hW s') τ
    have e3 := embT_eq a hH
    rw [e1, e2, e3] at h
    exact h
  refine Eq.trans ?_ (congrArg (fun t => t * φ (((d.colRec a).fm u).til c) s') (chi_ka a hS hH hP hQ u hM c).symm)
  refine Eq.trans ?_ (congrArg (fun t => d.σ₀ (((d.lev d.R.m).chr (d.tilMv u c).2 : d.X.Kˣ) : d.X.K) *
    φ (((d.colRec a).fm u).til c) t) hs)
  rfl

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQLift
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG

section QLiftS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

def qdPair {R : Type} [CommRing R] (k : GL (Fin n) R) : Matrix (Fin n) (Fin n) (R × R) :=
  fun i j => ((k : Matrix (Fin n) (Fin n) R) i j, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j i)

theorem qdPair_mul_inv {R : Type} [CommRing R] (k : GL (Fin n) R) : qdPair k * qdPair k⁻¹ = 1 := by
  have h1 : (k : Matrix (Fin n) (Fin n) R) * ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := Units.mul_inv k
  ext i j
  · show (∑ l, ((k : Matrix (Fin n) (Fin n) R) i l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i) *
        (((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l j, ((k⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j l)).1 = _
    rw [Prod.fst_sum]
    have := congrArg (fun A : Matrix (Fin n) (Fin n) R => A i j) h1
    simp only [Matrix.mul_apply] at this
    rw [Matrix.one_apply] at this ⊢
    simp only [Prod.fst_mul]
    rw [this]
    split_ifs <;> rfl
  · show (∑ l, ((k : Matrix (Fin n) (Fin n) R) i l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i) *
        (((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l j, ((k⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j l)).2 = _
    rw [Prod.snd_sum, inv_inv]
    have := congrArg (fun A : Matrix (Fin n) (Fin n) R => A j i) h1
    simp only [Matrix.mul_apply] at this
    simp only [Prod.snd_mul]
    rw [Matrix.one_apply] at this ⊢
    rw [show (∑ l, ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i * (k : Matrix (Fin n) (Fin n) R) j l) =
      ∑ l, (k : Matrix (Fin n) (Fin n) R) j l * ((k⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l i from
      Finset.sum_congr rfl fun l _ => mul_comm _ _, this]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]; rfl

def qdPairGL {R : Type} [CommRing R] (k : GL (Fin n) R) : GL (Fin n) (R × R) :=
  ⟨qdPair k, qdPair k⁻¹, qdPair_mul_inv k, by simpa using qdPair_mul_inv k⁻¹⟩

def qdLift (q : QLoc hc n Q Θ) (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)) : GL (Fin n) (E ⊗[F] (qv F P.1).adicCompletion F) :=
  bc (q.sp P).symm.toRingHom (qdPairGL k)

theorem qdf_sig_symm (q : QLoc hc n Q Θ) (P : Q) (a b : (qv F P.1).adicCompletion F) :
    sigR hc.sig ((qv F P.1).adicCompletion F) ((q.sp P).symm (a, b)) = (q.sp P).symm (b, a) := by
  apply (q.sp P).injective
  rw [q.sp_sig, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rfl

theorem qdLift_fst (q : QLoc hc n Q Θ) (P : Q) (k : GL (Fin n) ((qv F P.1).adicCompletion F)) :
    bc ((RingHom.fst _ _).comp (q.sp P).toRingHom) (qdLift q P k) = k := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((q.sp P) ((q.sp P).symm (qdPair k i j))).1 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem qdf_lift (q : QLoc hc n Q Θ) : QLift q := by
  intro P k hk
  refine ⟨qdLift q P k, ?_, ?_, qdLift_fst q P k⟩
  · show cT (sigR hc.sig ((qv F P.1).adicCompletion F)) ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *
        (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F)) * ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F))
    have hone : (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) ((qv F P.1).adicCompletion F)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have hcT : cT (sigR hc.sig ((qv F P.1).adicCompletion F)) ((qdLift q P k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) =
        ((qdLift q P k⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
      refine Matrix.ext fun i j => ?_
      show sigR hc.sig ((qv F P.1).adicCompletion F) ((q.sp P).symm (qdPair k j i)) = (q.sp P).symm (qdPair k⁻¹ i j)
      rw [qdf_sig_symm]
      rfl
    rw [hone, mul_one, hcT]
    rw [← Units.val_mul, qdLift, qdLift, ← map_mul]
    have : qdPairGL k⁻¹ * qdPairGL k = 1 := Units.ext (by
      have h := qdPair_mul_inv k⁻¹
      rw [inv_inv] at h
      exact h)
    rw [this, map_one, Units.val_one]
  · rw [rll_locL_std, Formalism.UG.P.afsplit_stab_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (q.sp P).symm (qdPair k i j) ∈ Formalism.BasicNotions.intV E (qv F P.1)
      rw [q.sp_int, RingEquiv.apply_symm_apply]
      exact ⟨hk.1 i j, hk.2 j i⟩
    · show (q.sp P).symm (qdPair k⁻¹ i j) ∈ Formalism.BasicNotions.intV E (qv F P.1)
      rw [q.sp_int, RingEquiv.apply_symm_apply]
      refine ⟨hk.2 i j, ?_⟩
      have e : (k⁻¹⁻¹ : GL (Fin n) ((qv F P.1).adicCompletion F)) = k := inv_inv k
      show ((↑(k⁻¹⁻¹) : Matrix (Fin n) (Fin n) ((qv F P.1).adicCompletion F)) j i) ∈ _
      rw [e]
      exact hk.1 j i

end QLiftS

end Formalism.L2.Col
end
end

