import Formalism.LocalToGlobal.Columns.Bundle0020
import Formalism.LocalToGlobal.Columns.TiedLv

-- bundled from Formalism.LocalToGlobal.Columns.TiedHDisc
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Crt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ST : Finset (Pl E)} {π : 𝓞 E} {T : ℕ}

def hd_fam (ST : Finset (Pl E)) : ST ⊕ ST → Ideal (𝓞 E) :=
  Sum.elim (fun P => P.1.asIdeal) (fun P => (conjPrime₂ P.1).asIdeal)

theorem hd_fam_coprime (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    Pairwise fun i j : ST ⊕ ST => IsCoprime (hd_fam ST i) (hd_fam ST j) := by
  have hmax : ∀ i, (hd_fam ST i).IsMaximal := by
    rintro (P | P)
    · exact P.1.isMaximal
    · exact (conjPrime₂ P.1).isMaximal
  have hinj : ∀ i j, hd_fam ST i = hd_fam ST j → i = j := by
    rintro (P | P) (Q | Q) h
    · exact congrArg Sum.inl (Subtype.ext (HeightOneSpectrum.ext h))
    · exact absurd (HeightOneSpectrum.ext h : P.1 = conjPrime₂ Q.1) (hc Q P)
    · exact absurd (HeightOneSpectrum.ext h : conjPrime₂ P.1 = Q.1).symm (hc P Q)
    · have h1 : conjPrime₂ P.1 = conjPrime₂ Q.1 := HeightOneSpectrum.ext h
      have h2 : P.1 = Q.1 := by rw [← rlh_conjP_conjP P.1, h1, rlh_conjP_conjP]
      exact congrArg Sum.inr (Subtype.ext h2)
  intro i j hij
  rw [Ideal.isCoprime_iff_sup_eq]
  exact Ideal.IsMaximal.coprime_of_ne (hmax i) (hmax j) fun h => hij (hinj i j h)

def hd_red (ST : Finset (Pl E)) :
    𝓞 E →ₗ[𝓞 E] ((∀ P : ST, 𝓞 E ⧸ P.1.asIdeal) × (∀ P : ST, 𝓞 E ⧸ (conjPrime₂ P.1).asIdeal)) :=
  LinearMap.prod (LinearMap.pi fun P : ST => Submodule.mkQ P.1.asIdeal)
    (LinearMap.pi fun P : ST => Submodule.mkQ (conjPrime₂ P.1).asIdeal)

theorem hd_red_surjective (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) : Function.Surjective (hd_red ST) := by
  rintro ⟨c, c'⟩
  choose x hx using fun P : ST => Submodule.mkQ_surjective P.1.asIdeal (c P)
  choose x' hx' using fun P : ST => Submodule.mkQ_surjective (conjPrime₂ P.1).asIdeal (c' P)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal (hd_fam_coprime hc) (Sum.elim x x')
  refine ⟨r, Prod.ext (funext fun P => ?_) (funext fun P => ?_)⟩
  · show Submodule.mkQ P.1.asIdeal r = c P
    rw [← hx P]
    exact (Submodule.Quotient.eq _).2 (hr (Sum.inl P))
  · show Submodule.mkQ (conjPrime₂ P.1).asIdeal r = c' P
    rw [← hx' P]
    exact (Submodule.Quotient.eq _).2 (hr (Sum.inr P))

theorem hd_red_ker (hB : BasePi ST π) (hT : π * cO E π = (T : 𝓞 E)) :
    LinearMap.ker (hd_red ST) = Ideal.span {(T : 𝓞 E)} := by
  ext r
  rw [LinearMap.mem_ker, Ideal.mem_span_singleton, ← hT]
  constructor
  · intro h
    have h1 : ∀ P ∈ ST, r ∈ P.asIdeal := fun P hP =>
      (Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Prod.fst h) ⟨P, hP⟩)
    have h2 : ∀ P ∈ ST, cO E r ∈ P.asIdeal := fun P hP =>
      (mem_conjP P r).1 ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Prod.snd h) ⟨P, hP⟩))
    have d1 : π ∣ r := (hB.dvd r).1 h1
    have d2 : cO E π ∣ r := by
      obtain ⟨s, hs⟩ := (hB.dvd (cO E r)).1 h2
      refine ⟨cO E s, ?_⟩
      rw [← map_mul, ← hs, cO_cO]
    exact hB.cop.mul_dvd d1 d2
  · rintro ⟨s, rfl⟩
    refine Prod.ext (funext fun P => ?_) (funext fun P => ?_)
    · refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [mul_assoc]
      exact Ideal.mul_mem_right _ _ (hB.mem P.2)
    · refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_conjP P.1 _).2 ?_)
      rw [map_mul, map_mul, cO_cO, mul_comm (cO E π), mul_assoc]
      exact Ideal.mul_mem_right _ _ (hB.mem P.2)

theorem hd_crt (hB : BasePi ST π) (hT : π * cO E π = (T : 𝓞 E)) (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    Nonempty ((𝓞 E ⧸ Ideal.span {(T : 𝓞 E)}) ≃ₗ[𝓞 E]
      ((∀ P : ST, 𝓞 E ⧸ P.1.asIdeal) × (∀ P : ST, 𝓞 E ⧸ (conjPrime₂ P.1).asIdeal))) :=
  ⟨(Submodule.quotEquivOfEq _ _ (hd_red_ker hB hT).symm).trans ((hd_red ST).quotKerEquivOfSurjective (hd_red_surjective hc))⟩

theorem hd_Lsh_quot {n : ℕ} {SG : Finset (Pl E)} (dd : DecoSet E n ST SG) (hB : BasePi ST π) (hT : π * cO E π = (T : 𝓞 E))
    (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    Nonempty ((dd.1.Lsh ⧸ dd.1.L.submoduleOf dd.1.Lsh) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {(T : 𝓞 E)})) := by
  obtain ⟨e1⟩ := dd.2.Lsh_quot_L hc
  obtain ⟨e2⟩ := hd_crt hB hT hc
  exact ⟨e1.trans e2.symm⟩

end Crt

section Tr

variable {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

theorem hd_transport (e : M ≃ₗ[R] M') (A B : Submodule R M) (A' B' : Submodule R M') (hA : ∀ x, e x ∈ A' ↔ x ∈ A)
    (hB : ∀ x, e x ∈ B' ↔ x ∈ B) :
    Nonempty ((A ⧸ B.comap A.subtype) ≃ₗ[R] (A' ⧸ B'.comap A'.subtype)) := by
  let f : A ≃ₗ[R] A' :=
    { toFun := fun x => ⟨e x.1, (hA x.1).2 x.2⟩
      invFun := fun y => ⟨e.symm y.1, (hA _).1 (by rw [e.apply_symm_apply]; exact y.2)⟩
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul e r x.1)
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
  refine ⟨Submodule.Quotient.equiv _ _ f ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hB x.1).2 hx
  · intro hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    show e.symm y.1 ∈ B
    refine (hB _).1 ?_
    rw [e.apply_symm_apply]
    exact hy

end Tr

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem hd_Ld_eq (hS : SpStd d.toColBase) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    CF.Ld (d.colRec a) u i hi c = (d.repr u i c).1.Lsh := by
  show Formalism.L2.Forms.dualL (d.sp.cm.sig : d.X.E →+* d.X.E) (CF.gramN (d.colRec a) i hi) (CF.clsCrd (d.colRec a) u i hi c) = _
  rw [gramN_eq a hS i hi, clsCrd_eq a u i hi c]
  exact rlc_span_dualSet d.sp.cm (d.R.N i) _

theorem attDisc (hS : SpStd d.toColBase) (u : d.what₂.Word) : AtTDisc (d.colRec a) u := by
  intro i hi c
  obtain ⟨e1⟩ := hd_Lsh_quot (d.repr u i c) (basePi_of_ok d.hX d.hPr u) (d.hPr.piT_norm u)
    (fun P Q => (moveHyp_of_ok d.hPr u P).st Q)
  obtain ⟨e0⟩ := hd_transport ((CF.crdN (d.colRec a) i hi).restrictScalars (𝓞 d.host.E))
    (CH.Ld (d.colRec a) u i c) ((d.colRec a).clsLat u i c) (d.repr u i c).1.Lsh (d.repr u i c).1.L
    (fun x => by
      have h := hx_mem_Ld (D := d.colRec a) u i hi c x
      rw [hd_Ld_eq a hS u i hi c] at h
      exact h)
    (fun x => by
      have h := hx_mem_map (D := d.colRec a) hi ((d.colRec a).clsLat u i c) x
      rw [← hx_clsCrd, clsCrd_eq a u i hi c] at h
      exact h)
  exact ⟨e0.trans e1⟩

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedUpDnLoc
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt redFn resS)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem updn_den {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P) (a : E ⊗[F] Formalism.L2.Herm.Af F)
    (h : prV (E := E) v a ∈ Formalism.BasicNotions.intV E v) :
    ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ iA F E (algebraMap (𝓞 E) E t) * a ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨D, hD, hDa⟩ := levelaf_denom (E := E) a
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  set DE : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) D with hDE
  have hDE0 : DE ≠ 0 := by
    rw [hDE, Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hD
  have hI : (Ideal.span {p * DE} : Ideal (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hp0 hDE0
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) _ hI (Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v))
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (Formalism.L2.DIV.idS F (Ideal.span {p * DE})) (Formalism.L2.DIV.oToS F E t) =
      Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v) := hq
  have hd := Ideal.Quotient.eq.1 hq'
  unfold Formalism.L2.DIV.idS at hd
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hd
  obtain ⟨y, hy⟩ := hd
  have ht : Formalism.L2.DIV.oToS F E t = Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE := by
    rw [mul_assoc, ← map_mul, hy]; ring
  refine ⟨t, ?_, ?_⟩
  · intro htP
    have h1 := congrArg (resS F P) ht
    rw [map_add, map_mul, map_mul, Formalism.L2.DIV.lc_res_eps P v hov, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_oToS,
      Ideal.Quotient.eq_zero_iff_mem.2 htP, Ideal.Quotient.eq_zero_iff_mem.2 hp, mul_zero, zero_mul, add_zero] at h1
    exact zero_ne_one h1
  · have hC : ((Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = levelafC E D := by
      rw [Formalism.L2.DIV.levelafC_eq_incl, ← iA_coe, hDE, ← IsScalarTower.algebraMap_apply]
    rw [iA_coe, ht]
    have e : ((Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) * a = afsplitIE v (prV (E := E) v a) +
          ((y * Formalism.L2.DIV.oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * (levelafC E D * a) := by
      rw [afsplit_decomp, ← hC, Subring.coe_add, Subring.coe_mul, add_mul, mul_assoc]
      rfl
    rw [e]
    exact add_mem (afsplit_IE_int v _ h) (mul_mem (y * Formalism.L2.DIV.oToS F E p).2 hDa)

variable {n : ℕ}

theorem updn_prV_pullV {v : HeightOneSpectrum (𝓞 F)} {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') (z : Fin n → E) (i : Fin n) :
    prV (E := E) v (pullV x z i) = prV (E := E) v (pullV x' z i) := by
  have h' : bc (prV (E := E) v) x⁻¹ = bc (prV (E := E) v) x'⁻¹ := by rw [map_inv, map_inv, h]
  unfold pullV
  simp only [Matrix.mulVec, dotProduct]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h'

variable [StarRing E]

theorem localized_globalLattice_le {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) ≤ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) := by
  classical
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (mem_locP P _ z).1 hz
  have h1 : ∀ i, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧
      iA F E (algebraMap (𝓞 E) E t) * pullV x' (s • z) i ∈ Formalism.L2.Herm.intAf F E := fun i =>
    updn_den hov _ (by
      rw [← updn_prV_pullV h]
      exact afsplit_prV_int v _ ((mem_globLat x _).1 hsz i))
  choose t ht hti using h1
  have hT : (∏ i, t i) ∉ P.asIdeal := by
    intro hm
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
    exact ht i hi
  refine (mem_locP P _ z).2 ⟨(∏ i, t i) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hT hs, ?_⟩
  rw [mul_smul, mem_globLat]
  intro i
  rw [pullV_osmul, ← Finset.prod_erase_mul Finset.univ t (Finset.mem_univ i), map_mul, map_mul, mul_assoc]
  exact mul_mem (iA_mem _) (hti i)

theorem updn_mem_loc {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) = localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) :=
  le_antisymm (localized_globalLattice_le hov h) (localized_globalLattice_le hov h.symm)

theorem updn_red_loc {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') {z : Fin n → E}
    (hz : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) (i : Fin n) :
    redA P (pullV x z i) = redA P (pullV x' z i) := by
  have hz' : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) := localized_globalLattice_le hov h hz
  obtain ⟨s, hs, hsz⟩ := pullV_den hz
  obtain ⟨s', hs', hsz'⟩ := pullV_den hz'
  have hss : s * s' ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'
  have m1 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_comm s s', map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz i)
  have m2 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i ∈ Formalism.L2.Herm.intAf F E := by
    rw [map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz' i)
  apply mul_left_cancel₀ (mk_ne_zero hss)
  rw [redA_spec P hss m1, redA_spec P hss m2, ← sub_eq_zero, ← map_sub]
  refine Formalism.L2.DIV.resS_eq_zero_of_prV P v hov _ ?_
  show prV (E := E) v (iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i -
    iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i) = 0
  rw [map_sub, map_mul (prV (E := E) v), map_mul (prV (E := E) v), updn_prV_pullV h, sub_self]

variable [NeZero n] (ST SG : Finset (Pl E))

theorem updn_f_loc {v : HeightOneSpectrum (𝓞 F)} (P : ST) (hov : IsOver v P.1)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    (decoRaw ST SG x).f P = (decoRaw ST SG x').f P := by
  funext z
  show (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then redA P.1 (pullV x z (lastIdx n)) else 0) =
    (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))
      then redA P.1 (pullV x' z (lastIdx n)) else 0)
  rw [← updn_mem_loc hov h]
  by_cases hz : z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
  · rw [if_pos hz, if_pos hz, updn_red_loc hov h hz]
  · rw [if_neg hz, if_neg hz]

theorem updn_be_loc {v : HeightOneSpectrum (𝓞 F)} (w : SG) (hov : IsOver v w.1)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    (decoRaw ST SG x).be w = (decoRaw ST SG x').be w := by
  funext z
  show (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then fun i => redA w.1 (pullV x z i) else 0) =
    (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))
      then fun i => redA w.1 (pullV x' z i) else 0)
  rw [← updn_mem_loc hov h]
  by_cases hz : z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
  · rw [if_pos hz, if_pos hz]
    funext i
    exact updn_red_loc hov h hz i
  · rw [if_neg hz, if_neg hz]

structure Deco.SameOff (v : HeightOneSpectrum (𝓞 F)) (d d' : Deco E n ST SG) : Prop where
  N : ∀ Q : Pl E, ¬ IsOver v Q → localization₂ Q.asIdeal d.N = localization₂ Q.asIdeal d'.N
  f : ∀ Q : ST, ¬ IsOver v Q.1 → d.f Q = d'.f Q
  be : ∀ w : SG, ¬ IsOver v w.1 → d.be w = d'.be w

theorem updn_decoRaw_eq (v : HeightOneSpectrum (𝓞 F)) (x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : Deco.SameOff ST SG v (decoRaw ST SG y) (decoRaw ST SG x)) :
    decoRaw ST SG (y * rll_put n v (bc (prV (E := E) v) (y⁻¹ * x))) = decoRaw ST SG x := by
  have hv : bc (prV (E := E) v) (y * rll_put n v (bc (prV (E := E) v) (y⁻¹ * x))) = bc (prV (E := E) v) x := by
    rw [map_mul, rll_put_self, ← map_mul, mul_inv_cancel_left]
  have hw : ∀ Q : Pl E, ¬ IsOver v Q →
      bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) (y * rll_put n v (bc (prV (E := E) v) (y⁻¹ * x))) =
        bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) y := by
    intro Q hQ
    have hne : Formalism.L2.DIV.underPl F Q ≠ v := by
      rintro rfl; exact hQ rfl
    rw [map_mul, rll_put_ne n v _ hne, mul_one]
  ext1
  · refine Formalism.L2.DIV.eq_of_forall_localized_eq fun Q => ?_
    by_cases hQ : IsOver v Q
    · exact updn_mem_loc hQ hv
    · exact (updn_mem_loc (v := Formalism.L2.DIV.underPl F Q) rfl (hw Q hQ)).trans (h.N Q hQ)
  · funext Q
    by_cases hQ : IsOver v Q.1
    · exact updn_f_loc ST SG Q hQ hv
    · exact (updn_f_loc ST SG (v := Formalism.L2.DIV.underPl F Q.1) Q rfl (hw Q.1 hQ)).trans (h.f Q hQ)
  · funext w
    by_cases hQ : IsOver v w.1
    · exact updn_be_loc ST SG w hQ hv
    · exact (updn_be_loc ST SG (v := Formalism.L2.DIV.underPl F w.1) w rfl (hw w.1 hQ)).trans (h.be w hQ)

theorem Deco.SameOff.dia {v : HeightOneSpectrum (𝓞 F)} {d d' : Deco E n ST SG} (h : Deco.SameOff ST SG v d d')
    (c : DiaG E ST) : Deco.SameOff ST SG v (d.dia c) (d'.dia c) where
  N := h.N
  f Q hQ := by
    funext z
    show (c Q).1 * d.f Q z = (c Q).1 * d'.f Q z
    rw [h.f Q hQ]
  be := h.be

end Loc

section Move

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

theorem updn_move (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) (v : HeightOneSpectrum (𝓞 F)) (d d₁ d' : DecoSet E n ST SG)
    (h : Deco.SameOff ST SG v d.1 d₁.1) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d₁) :
    ∃ (γ : URat hc n) (η : UAd hc n) (κ : levU hc n ST SG H), ratHom hc n γ = g₀.1 ∧ levRed hc n ST SG H κ = g₀.2 ∧
      (∀ v', v' ≠ v → bc (prV (E := E) v') (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
      bc (iA F E) (γ : GL (Fin n) E) * (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (ptOfD hc n ST SG c₀ d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * η * κ := by
  set y := ptOfD hc n ST SG c₀ d with hy
  set x := ptOfD hc n ST SG c₀ d₁ with hx
  have hdy : decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.dia c₀⁻¹ := decoOf_ptOf hc n ST SG hS _
  have hdx : decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.dia c₀⁻¹ := decoOf_ptOf hc n ST SG hS _
  have hry : decoRaw ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.1.dia c₀⁻¹ := by
    rw [← rlc_decoOf_val hc n ST SG y.2, hdy]; rfl
  have hrx : decoRaw ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.1.dia c₀⁻¹ := by
    rw [← rlc_decoOf_val hc n ST SG x.2, hdx]; rfl
  let η : UAd hc n := ⟨rll_put n v (bc (prV (E := E) v) ((y⁻¹ * x : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))),
    rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (y⁻¹ * x).2)⟩
  have key : decoOf ST SG ((y * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      g₀ • decoOf ST SG (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have h1 : decoOf ST SG ((y * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.dia c₀⁻¹ := by
      apply Subtype.ext
      rw [rlc_decoOf_val hc n ST SG (y * η).2]
      refine Eq.trans ?_ hrx
      exact updn_decoRaw_eq ST SG v _ _ (by rw [hry, hrx]; exact h.dia ST SG c₀⁻¹)
    rw [h1]
    unfold ptOfD
    rw [decoOf_ptOf hc n ST SG hS, ← hg₀]
    exact rla_dia_smulH n ST SG H c₀⁻¹ g₀ d'
  obtain ⟨γ, κ, hγ, hκ, e⟩ := rlc_rel_of_orbit hc n ST SG H g₀ key
  refine ⟨γ, η, κ, hγ, hκ, fun v' hv' => rll_put_ne n v v' hv' _, ?_⟩
  rw [← Subgroup.coe_mul, e, inv_mul_cancel_right]

end Move

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ValuationPosIffMemSeen
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

open Classical in

theorem th_pull_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) :
    pullW (tauOfR hX hPr u w P) w = if seenC Pr u w then P.1 else conjPrime₂ P.1 := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dif_pos hw]
    rfl
  rw [e]
  by_cases hs : seenC Pr u w
  · rw [if_pos hs]
    exact (tauOfC_spec hX hPr u w hw P).resolve_right (hs.not_bar hPr _ P)
  · rw [if_neg hs]
    refine (tauOfC_spec hX hPr u w hw P).resolve_left fun h => hs (seenC_of_one hPr (τ := tauOfC w P.1) ?_)
    rw [show pullW (tauOfC w P.1) w = P.1 from h]
    exact P.2

end Gen

variable {d : ColDat} (a : ColArgs d)

open Classical in
theorem valuation_pos_iff_mem_seen (hH : HostHyp d) (u : d.what₂.Word) (w : d.what₂.places.Pl) (hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal)
    (v : {P // P ∈ d.Pr.vT u}) (x : 𝓞 d.X.E) :
    (0 : WithTop ℤ) < d.what₂.places.val w ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K) ↔
      x ∈ (if decide (seenC d.Pr u (d.plEq w)) = true then v.1.asIdeal else conjIdeal (K := d.X.E) v.1.asIdeal) := by
  rw [att_val_pos d.what₂.places d.plEq hH.val_eq w]
  have h1 : d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x ∈ (d.plEq w).asIdeal ↔
      x ∈ (pullW (tauOfR d.hX d.hPr u (d.plEq w) v) (d.plEq w)).asIdeal := Iff.rfl
  rw [h1, th_pull_tauOf d.hX d.hPr u (d.plEq w) hT v]
  by_cases hs : seenC d.Pr u (d.plEq w)
  · rw [if_pos hs, if_pos (decide_eq_true hs)]
  · rw [if_neg hs, if_neg (by simpa using hs), conjIdeal_asIdeal]

theorem th_seen (hH : HostHyp d) (u : d.what₂.Word) : AtTSeen (atTTied a hH u) := by
  intro w hw v x y hy
  have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
    have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
    rw [hw] at this
    exact this
  have hy' : y = ((d.X.embO (tauOfR d.hX d.hPr u (d.plEq w) v) x : 𝓞 d.X.K) : d.X.K) := by
    apply d.what₂.embLL.injective
    rw [hy]
    show d.host.φ₀ _ = d.what₂.embLL (d.embE _)
    rw [← hH.embE_φ₀]
    rfl
  have hPv : (atTTied a hH u).Pv v = v.1.asIdeal := lv_Pv_eq a hH u v
  rw [hy', hPv]
  exact valuation_pos_iff_mem_seen hH u w hT v x

end Formalism.L2.Col
end
end

