import Formalism.LocalToGlobal.Columns.Bundle0011
import Formalism.LocalToGlobal.Columns.DGamAut
import Formalism.LocalToGlobal.Columns.Bundle0015
import Formalism.LocalToGlobal.Columns.Bundle0017
import Mathlib

-- bundled from Formalism.LocalToGlobal.Columns.ChainFrmOk
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem frm_exists_c (p p0 : DecoF X.E n ST SG Q) (h : p.deco = p0.deco) :
    ∃ c : GLQ X.E n Q, p = ((1, 1, c) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • p0 := by
  refine ⟨fun P => ⟨(p.fr P)⁻¹ * p0.fr P, ?_⟩, ?_⟩
  · show ∀ x, ((p.fr P)⁻¹ * p0.fr P) x ∈ stdAt X.E n P.1 ↔ x ∈ stdAt X.E n P.1
    intro x
    have hx : p.1.2 P (((p.fr P)⁻¹ * p0.fr P) x) = p0.1.2 P x := LinearEquiv.apply_symm_apply _ _
    have h' : p.1.1 = p0.1.1 := h
    rw [← p.2 P, hx, h', p0.2 P]
  · apply Subtype.ext
    simp only [HSMul.hSMul, SMul.smul]
    refine Prod.ext ?_ ?_
    · have h1 := one_smul (UF X.E n × GLG X.E n SG) p0.1.1
      simp only [HSMul.hSMul, SMul.smul] at h1
      exact h.trans h1.symm
    · funext P
      simp only [DecoF.fr, OneMemClass.coe_one, one_mul, InvMemClass.coe_inv, _root_.mul_inv_rev, inv_inv,
        ← mul_assoc, mul_inv_cancel]

variable (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)

theorem frm_root (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) ^ m = 1 := by
  haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  obtain ⟨m2, hm2, h2⟩ := hroot g.2.2
  have hfo : IsOfFinOrder g.2.1 := isOfFinOrder_of_finite _
  have ha : ((Λ.chr g.2.1 : X.Kˣ) : X.K) ^ orderOf g.2.1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  refine ⟨orderOf g.2.1 * m2, Nat.mul_pos hfo.orderOf_pos hm2, ?_⟩
  rw [Units.val_mul, mul_pow, pow_mul, ha, one_pow, one_mul, mul_comm (orderOf _) m2, pow_mul, h2,
    one_pow]

open Classical in

theorem frmGSD_ok_of_finIdx (hX : X.Ok) (C : CoefPk X n (DecoSet X.E n ST SG)) (hC : C.Eqv)
    (hfi : ∀ P : Q, Finite (↥(GLint X.E n P.1) ⧸ (Θ P).H))
    (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) : (frmGSD (C.pull DecoF.deco) Λ Θ).Ok where
  fin_orb := by
    obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs

    let pt : s → (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) → Option (DecoF X.E n ST SG Q) := fun d cb =>
      if h : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d.1 then
        some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • h.choose) else none
    have hfin : Finite (Option (s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H))) := inferInstance
    by_cases hne : Nonempty (frmGSD (C.pull DecoF.deco) Λ Θ).Cl
    swap
    · have := not_nonempty_iff.1 hne
      exact inferInstance
    obtain ⟨c00⟩ := hne
    refine Finite.of_surjective (fun a : s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) =>
      match pt a.1 a.2 with
      | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
      | none => c00) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)

      let p1 : DecoF X.E n ST SG Q := ((g, 1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q)⁻¹ • p
      have hp1 : p1.deco = d0 := by
        show ((g, (1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG)⁻¹ • p.deco = d0
        rw [hg, inv_smul_smul]
      have hex : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d0 := ⟨p1, hp1⟩
      obtain ⟨c, hc⟩ := frm_exists_c p1 hex.choose (hp1.trans hex.choose_spec.symm)

      let cb : ∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H := fun P => QuotientGroup.mk ((c P)⁻¹)
      have hout : ∀ P : Q, ((c P)⁻¹)⁻¹ * (cb P).out ∈ (Θ P).H := fun P => QuotientGroup.eq.1 (QuotientGroup.out_eq' (cb P)).symm
      refine ⟨(⟨d0, hd0⟩, cb), ?_⟩
      have hpt : pt ⟨d0, hd0⟩ cb = some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • hex.choose) := dif_pos hex
      show (match pt ⟨d0, hd0⟩ cb with
        | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
        | none => c00) = _
      rw [hpt]
      let θ : ↥Θ.grp := ⟨fun P => ((c P)⁻¹)⁻¹ * (cb P).out, fun P _ => hout P⟩
      refine ((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff _ p).mpr ⟨((g, 1, θ) : FrmG Λ Θ)⁻¹, ?_⟩
      refine inv_smul_eq_iff.2 (Eq.symm ?_)
      show ((g, (1 : GLG X.E n SG), (θ : GLQ X.E n Q)) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) •
        (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • hex.choose) = p
      rw [← mul_smul]
      have e : ((g, (1 : GLG X.E n SG), (θ : GLQ X.E n Q)) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) * (1, 1, fun P => ((cb P).out)⁻¹) =
          (g, 1, 1) * (1, 1, c) := by
        refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
        funext P
        show ((c P)⁻¹)⁻¹ * (cb P).out * ((cb P).out)⁻¹ = 1 * c P
        group
      rw [e, mul_smul, ← hc]
      exact smul_inv_smul _ p
  fin_stab := by
    intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet X.E n ST SG)
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p =>
        (⟨(a.1.1, (a.1.2.1 : GLG X.E n SG)), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG X.E n SG) (DecoF.deco p : DecoSet X.E n ST SG))) ?_
    intro a b hab
    have h0 : ((a.1.1, (a.1.2.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) = (b.1.1, (b.1.2.1 : GLG X.E n SG)) :=
      congrArg Subtype.val hab
    exact Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 (Prod.mk.inj h0).1)
  nab_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.nab_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  del_smul := by
    intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.del_smul (g.1, (g.2.1 : GLG X.E n SG)) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  inv := by
    intro g (x : C.V) (y : C.V)
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x)
      ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem chF_ok_of_finIdx (hX : X.Ok) (u : Pr.Word) (j : ℕ)
    (hfi : ∀ (b : L.β j) (P : QE sel (mu : Chr X.F X.E X.K)), Finite (↥(GLint X.E (R.N j) P.1) ⧸ (L.levQ j b P).H))
    (hroot : ∀ (b : L.β j) (c : ↥(L.levQ j b).grp), ∃ m : ℕ, 0 < m ∧ (((L.levQ j b).chr c : X.Kˣ) : X.K) ^ m = 1) :
    (chF W sel mu L u j).Ok := fun b =>
  frmGSD_ok_of_finIdx (L.levG j b) (L.levQ j b) hX (colVal W u j (Pr.vT u) Pr.vGs)
    (colVal_eqv W hX u j _ _) (hfi b) (hroot b)

end Chain

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.HxMemMap
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec}

theorem hx_hform (i : ℕ) (hi : i ≤ D.R.m) (x y : (D.sp.X i).V) :
    (D.sp.X i).hT x y = hform (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi) (CF.crdN D i hi x) (CF.crdN D i hi y) := by
  rw [Formalism.L2.Herm.hT_crd D.sp.cm (D.sp.X i) x y]
  unfold hform
  rw [← (finCongr (CF.rankN D i hi)).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (finCongr (CF.rankN D i hi)).symm.sum_comp]
  exact Finset.sum_congr rfl fun b _ => rfl

variable (u : D.what₂.Word)

theorem hx_clsCrd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.clsCrd D u i hi c = (D.clsLat u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := rfl

theorem hx_Ld_eq (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.Ld D u i hi c = (CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  have key : (((CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (CF.sigD D : D.host.E →+* D.host.E) (CF.gramN D i hi) (CF.clsCrd D u i hi c) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩ s ⟨y, hy, rfl⟩
      have := (Formalism.L2.Herm.mem_dual (D.sp.X i) (D.clsLat u i c) x).1 hx y hy
      rw [hx_hform i hi] at this
      exact this
    · intro ht
      refine ⟨(CF.crdN D i hi).symm t, ?_, (CF.crdN D i hi).apply_symm_apply t⟩
      refine (Formalism.L2.Herm.mem_dual (D.sp.X i) (D.clsLat u i c) _).2 fun y hy => ?_
      rw [hx_hform i hi, LinearEquiv.apply_symm_apply]
      exact ht (CF.crdN D i hi y) ⟨y, hy, rfl⟩
  show Submodule.span (𝓞 D.host.E) (dualSet _ _ _) = _
  rw [← key, Submodule.span_eq]

theorem hx_mem_map {i : ℕ} (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (D.sp.X i).V) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ M.map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) ↔ x ∈ M := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := (CF.crdN D i hi).injective e
    exact this ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

theorem hx_mem_Ld (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ CF.Ld D u i hi c ↔ x ∈ CH.Ld D u i c := by
  rw [hx_Ld_eq, hx_mem_map]

theorem hx_smul_Ld (I : Ideal (𝓞 D.host.E)) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    I • CF.Ld D u i hi c = (I • CH.Ld D u i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  rw [hx_Ld_eq, Submodule.map_smul'']

theorem hx_Lk_eq (I : Ideal (𝓞 D.host.E)) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    CF.clsCrd D u i hi c ⊔ I • CF.Ld D u i hi c = (CH.Lk D u I i c).map
      ((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  rw [hx_smul_Ld, hx_clsCrd, ← Submodule.map_sup]

variable {u} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

theorem hx_mem_Lk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (x : (D.sp.X i).V) :
    CF.crdN D i hi x ∈ CF.Lk A i hi v c ↔ x ∈ CH.Lk D u (A.Pv v) i c := by
  show CF.crdN D i hi x ∈ CF.clsCrd D u i hi c ⊔ A.Pv v • CF.Ld D u i hi c ↔ _
  rw [hx_Lk_eq, hx_mem_map]

def hxLd (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) : ↥(CH.Ld D u i c) →+ ↥(CF.Ld D u i hi c) where
  toFun z := ⟨CF.crdN D i hi z.1, (hx_mem_Ld u i hi c z.1).2 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

def hxLk (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    ↥(CH.Lk D u (A.Pv v) i c) →+ ↥(CF.Lk A i hi v c) where
  toFun z := ⟨CF.crdN D i hi z.1, (hx_mem_Lk A i hi v c z.1).2 z.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

open Classical in

def hxPr (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : ↥(CH.Ld D u i c) →+ (D.fm u).lv i v c :=
  if hi : i ≤ D.R.m then ((P i hi).pr v c).comp (hxLd i hi c) else 0

open Classical in

def hxPrk (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : ↥(CH.Lk D u (A.Pv v) i c) →+ (D.fm u).lk i v c :=
  if hi : i ≤ D.R.m then ((P i hi).prk v c).comp (hxLk A i hi v c) else 0

theorem hxPr_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c z = (P i hi).pr v c (hxLd i hi c z) := by
  unfold hxPr; rw [dif_pos hi]; rfl

theorem hxPrk_eq (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c z = (P i hi).prk v c (hxLk A i hi v c z) := by
  unfold hxPrk; rw [dif_pos hi]; rfl

theorem hxPr_surj (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Function.Surjective (hxPr A P i v c) := by
  intro q
  obtain ⟨z, rfl⟩ := (P i hi).pr_surj v c q
  refine ⟨⟨(CF.crdN D i hi).symm z.1, (hx_mem_Ld u i hi c _).1 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
  rw [hxPr_eq A P i hi]
  congr 1
  exact Subtype.ext ((CF.crdN D i hi).apply_symm_apply z.1)

theorem hxPr_smul (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (r : 𝓞 D.host.E) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c (r • z) = A.res v r • hxPr A P i v c z := by
  by_cases hi : i ≤ D.R.m
  · rw [hxPr_eq A P i hi, hxPr_eq A P i hi, ← (P i hi).pr_smul]
    congr 1
    exact Subtype.ext (((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
      (𝓞 D.host.E)).map_smul r z.1)
  · unfold hxPr; rw [dif_neg hi]; simp

theorem hxPr_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    hxPr A P i v c z = 0 ↔ z.1 ∈ A.Pv v • CH.Ld D u i c := by
  rw [hxPr_eq A P i hi, (P i hi).pr_ker, hx_smul_Ld]
  exact hx_mem_map hi _ z.1

theorem hx_fv_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c)) :
    (D.fm u).fv i v c (hxPr A P i v c z) = 0 ↔ z.1 ∈ CH.Lk D u (A.Pv v) i c := by
  rw [hxPr_eq A P i hi, (P i hi).fv_ker]
  exact hx_mem_Lk A i hi v c z.1

theorem hxPrk_surj (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Function.Surjective (hxPrk A P i v c) := by
  intro q
  obtain ⟨z, rfl⟩ := (P i hi).prk_surj v c q
  refine ⟨⟨(CF.crdN D i hi).symm z.1, (hx_mem_Lk A i hi v c _).1 (by rw [LinearEquiv.apply_symm_apply]; exact z.2)⟩, ?_⟩
  rw [hxPrk_eq A P i hi]
  congr 1
  exact Subtype.ext ((CF.crdN D i hi).apply_symm_apply z.1)

theorem hxPrk_smul (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (r : 𝓞 D.host.E) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c (r • z) = A.res v r • hxPrk A P i v c z := by
  by_cases hi : i ≤ D.R.m
  · rw [hxPrk_eq A P i hi, hxPrk_eq A P i hi, ← (P i hi).prk_smul]
    congr 1
    exact Subtype.ext (((CF.crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars
      (𝓞 D.host.E)).map_smul r z.1)
  · unfold hxPrk; rw [dif_neg hi]; simp

theorem hxPrk_ker (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Lk D u (A.Pv v) i c)) :
    hxPrk A P i v c z = 0 ↔ z.1 ∈ A.Pv v • CH.Lk D u (A.Pv v) i c := by
  rw [hxPrk_eq A P i hi, (P i hi).prk_ker]
  show CF.crdN D i hi z.1 ∈ A.Pv v • (CF.clsCrd D u i hi c ⊔ A.Pv v • CF.Ld D u i hi c) ↔ _
  rw [hx_Lk_eq, ← Submodule.map_smul'']
  exact hx_mem_map hi _ z.1

theorem hx_te (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(CH.Ld D u i c))
    (hz : (D.fm u).fv i v c (hxPr A P i v c z) = 1)
    (h : ((D.mem u).A.T : D.host.E) • z.1 ∈ CH.Lk D u (A.Pv v) i c) :
    hxPrk A P i v c ⟨_, h⟩ = (D.fm u).te i v c := by
  rw [hxPr_eq A P i hi] at hz
  have e : CF.crdN D i hi (((D.mem u).A.T : D.host.E) • z.1) = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (hxLd i hi c z).1 := by
    rw [map_smul]
    show _ = (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • CF.crdN D i hi z.1
    rw [Algebra.smul_def' , map_natCast] <;> rfl
  have h' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (hxLd i hi c z).1 ∈ CF.Lk A i hi v c := by
    rw [← e]; exact (hx_mem_Lk A i hi v c _).2 h
  rw [hxPrk_eq A P i hi, ← (P i hi).te v c (hxLd i hi c z) hz h']
  congr 1
  exact Subtype.ext e

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.SummandSlopeOfThreeLemmas
section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Defs

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

@[reducible] def latK (M : Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (Pi.basisFun K (Fin n)) M (formAt (Pi.basisFun K (Fin n)) (hStd K n))

@[reducible] def weylH (lam : DomWeight n) (M : Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (bVV K (oneW lam)) (delK (oneW lam) fun _ => M) (formAt (bVV K (oneW lam)) (stdPair K lam))

@[reducible] def tenH {ι : Type} [Fintype ι] (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (bVV K lam) (delK lam M) (formAt (bVV K lam) (pairK lam fun _ => 1))

theorem weylH_std (lam : DomWeight n) : weylH K lam (colLat (1 : GL (Fin n) K)) = stdDelH K lam := by
  unfold weylH stdDelH
  rw [stdDelL_eq]

def WeylFunct : Prop :=
  ∀ (n : ℕ) (lam : DomWeight n) (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsLattice K M →
    (weylH K lam M).mu = ((∑ i, lam.w i : ℤ) : ℝ) * (latK K M).mu + (stdDelH K lam).mu

def TensorSlope : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)),
    (∀ τ, Submodule.IsLattice K (M τ)) → (tenH K lam M).mu = ∑ τ, (weylH K (lam τ) (M τ)).mu

end Defs

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def EEC (u : Pr.Word) (d : (colGSD W Ch u 0).D) (τ : X.Tau) : Submodule (𝓞 X.K) (Fin (R.N 0) → X.K) :=
  dualFr (tauLat X.emb τ (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh)

theorem EEC_isLattice (u : Pr.Word) (d : (colGSD W Ch u 0).D) (τ : X.Tau) : Submodule.IsLattice X.K (EEC W Ch u d τ) := by
  unfold EEC
  have hL : Submodule.IsLattice X.E (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).1.Lsh :=
    (d : DecoSet X.E (R.N 0) (Pr.vT u) Pr.vGs).2.Lsh_lattice
  exact (dualFrameLattice_holds X.K (R.N 0) 1 _ (by simp)
    (tauLatticeLattice_holds X.E X.K X.Tau (R.N 0) X.emb τ _ hL)).1

theorem colValH_eq_tenH (u : Pr.Word) (d : (colGSD W Ch u 0).D) :
    (colGSD W Ch u 0).valH d = tenH X.K (W.lamTrue u 0) (EEC W Ch u d) := by
  have hg : gramKd X.emb (1 : Matrix (Fin (R.N 0)) (Fin (R.N 0)) X.E) = fun _ => 1 := by
    funext τ
    simp [gramKd]
  have hpair : (colGSD W Ch u 0).pair = pairK (W.lamTrue u 0) fun _ => 1 := by
    show pairVr X.emb (W.lamTrue u 0) 1 = _
    rw [pairVr, hg]
  have hform : (fun v => (colGSD W Ch u 0).pairAt v) =
      formAt (bVV X.K (W.lamTrue u 0)) (pairK (W.lamTrue u 0) fun _ => 1) := by
    funext v x y
    rw [GSD.pairAt_eq_formAt, hpair]
    rfl
  show ofFormB (colGSD W Ch u 0).bV ((colGSD W Ch u 0).Del d) (fun v => (colGSD W Ch u 0).pairAt v) = _
  rw [hform]
  rfl

def EESlope (u : Pr.Word) : Prop :=
  ∀ (d : (colGSD W Ch u 0).D) (τ : X.Tau), (latK X.K (EEC W Ch u d τ)).mu = -(logTC Pr u) / (R.k : ℝ)

end Cols

end Formalism.L2.Col
end
end

