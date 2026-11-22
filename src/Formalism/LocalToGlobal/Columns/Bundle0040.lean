import Formalism.LocalToGlobal.Columns.Bundle0038
import Mathlib
import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
import Formalism.LocalToGlobal.Columns.ChainOneB
import Formalism.LocalToGlobal.Columns.Bundle0023

-- bundled from Formalism.LocalToGlobal.Columns.DecoratedFrameDiagonalTwistDecoration
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Fr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.SameOn (B : Finset (HeightOneSpectrum (𝓞 E))) (d d' : DecoSet E n ST SG) : Prop := ∀ P ∈ B, d'.1.at P = d.1.at P

theorem DecoSet.SameOn.smul {B : Finset (HeightOneSpectrum (𝓞 E))} {d d' : DecoSet E n ST SG} (h : DecoSet.SameOn B d d')
    (a : UF E n × GLG E n SG) : DecoSet.SameOn B (a • d) (a • d') := by
  intro P hP
  have e : localization₂ P.asIdeal d'.1.N = localization₂ P.asIdeal d.1.N := h P hP
  rw [DecoSet.smul_val, DecoSet.smul_val]
  ext x
  show x ∈ localization₂ P.asIdeal (gmap a.1.1 d'.1.N) ↔ x ∈ localization₂ P.asIdeal (gmap a.1.1 d.1.N)
  rw [mem_localization_gmap, mem_localization_gmap, e]

theorem DecoSet.SameOn.of_smul {B : Finset (HeightOneSpectrum (𝓞 E))} {d d' : DecoSet E n ST SG} (a : UF E n × GLG E n SG)
    (h : DecoSet.SameOn B (a • d) (a • d')) : DecoSet.SameOn B d d' := by
  have h2 := h.smul a⁻¹
  simpa only [inv_smul_smul] using h2

def DecoF.repl (p : DecoF E n ST SG Q) (d' : DecoSet E n ST SG) (h : DecoSet.SameOn Q p.deco d') : DecoF E n ST SG Q :=
  ⟨(d', p.1.2), fun P x => by rw [h P.1 P.2]; exact p.2 P x⟩

open Classical in

def DecoF.mv (p : DecoF E n ST SG Q) (d' : DecoSet E n ST SG) : DecoF E n ST SG Q :=
  if h : DecoSet.SameOn Q p.deco d' then p.repl d' h else p

theorem DecoF.mv_pos {p : DecoF E n ST SG Q} {d' : DecoSet E n ST SG} (h : DecoSet.SameOn Q p.deco d') : p.mv d' = p.repl d' h := by
  unfold DecoF.mv; rw [dif_pos h]

theorem DecoF.mv_neg {p : DecoF E n ST SG Q} {d' : DecoSet E n ST SG} (h : ¬ DecoSet.SameOn Q p.deco d') : p.mv d' = p := by
  unfold DecoF.mv; rw [dif_neg h]

theorem DecoF.mv_deco {p : DecoF E n ST SG Q} {d' : DecoSet E n ST SG} (h : DecoSet.SameOn Q p.deco d') : (p.mv d').deco = d' := by
  rw [DecoF.mv_pos h]; rfl

theorem DecoF.mv_fr (p : DecoF E n ST SG Q) (d' : DecoSet E n ST SG) (P : Q) : (p.mv d').fr P = p.fr P := by
  unfold DecoF.mv; split_ifs <;> rfl

theorem DecoF.smul_deco (g : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) : (g • p).deco = (g.1, g.2.1) • p.deco := rfl

theorem DecoF.mv_smul (g : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) (d' : DecoSet E n ST SG) :
    (g • p).mv ((g.1, g.2.1) • d') = g • p.mv d' := by
  by_cases h : DecoSet.SameOn Q p.deco d'
  · have h' : DecoSet.SameOn Q (g • p).deco ((g.1, g.2.1) • d') := by
      rw [DecoF.smul_deco]; exact h.smul _
    rw [DecoF.mv_pos h', DecoF.mv_pos h]
    apply Subtype.ext; apply Prod.ext
    · exact (DecoF.smul_deco g (p.repl d' h)).symm
    · rfl
  · have h' : ¬ DecoSet.SameOn Q (g • p).deco ((g.1, g.2.1) • d') := by
      rw [DecoF.smul_deco]; exact fun hh => h (DecoSet.SameOn.of_smul _ hh)
    rw [DecoF.mv_neg h', DecoF.mv_neg h]

theorem DecoSet.sameOn_diagonalTwist (B : Finset (HeightOneSpectrum (𝓞 E))) (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (d : DecoSet E n ST SG) :
    DecoSet.SameOn B d (d.dia1 P a) := fun _ _ => rfl

theorem DecoSet.sameOn_up {B : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet E n ST SG) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    (hB : ∀ P' ∈ B, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (q : 𝓞 E) {x : Sp E n} (hx : x ∈ d.1.N) : DecoSet.SameOn B d (d.up P q x) := by
  intro P' hP'
  unfold DecoSet.up
  split_ifs with hok
  · show localization₂ P'.asIdeal (upN P.1.asIdeal d.1.N x) = localization₂ P'.asIdeal d.1.N
    exact ((upN_spec d.2.lat d.2.uni P.1 hne hx).2.2.1 P' (hB P' hP').1 (hB P' hP').2).localization_eq
  · rfl

theorem DecoSet.sameOn_dn {B : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet E n ST SG) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    (hB : ∀ P' ∈ B, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal) : DecoSet.SameOn B d (d.dn P f') := by
  intro P' hP'
  unfold DecoSet.dn
  split_ifs with hok
  · show localization₂ P'.asIdeal (d.1.dnN P) = localization₂ P'.asIdeal d.1.N
    exact ((d.2.dnN_spec P hne).2.2.1 P' (hB P' hP').1 (hB P' hP').2).localization_eq
  · rfl

def DecoF.dia1 (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (p : DecoF E n ST SG Q) : DecoF E n ST SG Q := ⟨(p.1.1.dia1 P a, p.1.2), p.2⟩

theorem DecoF.decoratedFrame_diagonalTwist_decoration (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (p : DecoF E n ST SG Q) : (p.dia1 P a).deco = p.deco.dia1 P a := rfl

theorem DecoF.decoratedFrame_diagonalTwist_frame (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (p : DecoF E n ST SG Q) (P' : Q) : (p.dia1 P a).fr P' = p.fr P' := rfl

theorem DecoF.decoratedFrame_diagonalTwist_eq_move (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (p : DecoF E n ST SG Q) : p.dia1 P a = p.mv (p.deco.dia1 P a) := by
  rw [DecoF.mv_pos (DecoSet.sameOn_diagonalTwist Q P a p.deco)]; rfl

theorem DecoF.decoratedFrame_diagonalTwist_smul (P : ST) (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) (g : UF E n × GLG E n SG × GLQ E n Q) (p : DecoF E n ST SG Q) :
    (g • p).dia1 P a = g • p.dia1 P a := rfl

def DecoF.upL (p : DecoF E n ST SG Q) (P : ST) (q : 𝓞 E) (x : p.deco.lv P) : DecoF E n ST SG Q := p.mv (p.deco.upL P q x)

def DecoF.dnL (p : DecoF E n ST SG Q) (P : ST) (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (p.deco.lk P)) : DecoF E n ST SG Q := p.mv (p.deco.dnL P g)

theorem DecoF.upL_deco (p : DecoF E n ST SG Q) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) (hQ : ∀ P' ∈ Q, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (q : 𝓞 E)
    (x : p.deco.lv P) : (p.upL P q x).deco = p.deco.upL P q x := by
  exact DecoF.mv_deco (DecoSet.sameOn_up p.deco P hne hQ q (x := modP.rep x) (Quotient.out x).2)

theorem DecoF.dnL_deco (p : DecoF E n ST SG Q) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) (hQ : ∀ P' ∈ Q, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1)
    (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (p.deco.lk P)) : (p.dnL P g).deco = p.deco.dnL P g := by
  exact DecoF.mv_deco (DecoSet.sameOn_dn p.deco P hne hQ _)

theorem DecoF.upL_fr (p : DecoF E n ST SG Q) (P : ST) (q : 𝓞 E) (x : p.deco.lv P) (P' : Q) : (p.upL P q x).fr P' = p.fr P' := by
  exact DecoF.mv_fr p _ P'

theorem DecoF.dnL_fr (p : DecoF E n ST SG Q) (P : ST) (g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (p.deco.lk P)) (P' : Q) :
    (p.dnL P g).fr P' = p.fr P' := by
  exact DecoF.mv_fr p _ P'

end Fr

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem locLat_sameAt {E : Type} [Field E] [NumberField E] {n : ℕ} (SB : Finset (HeightOneSpectrum (𝓞 E))) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ P ∈ SB, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) (e : SB → ℤ) : locLat SB N' e = locLat SB N e := by
  unfold locLat
  exact iInf_congr fun P => by rw [h P.1 P.2]

theorem ybSet_sameAt {n : ℕ} {N N' : Submodule (𝓞 X.E) (Sp X.E n)} (h : ∀ P ∈ rowSG Pr sel mu, localization₂ P.asIdeal N' = localization₂ P.asIdeal N) :
    ybSet sel mu cst N' = ybSet sel mu cst N := by
  unfold ybSet
  rw [locLat_sameAt _ h, locLat_sameAt _ h]

end Yb

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.DetChrLeaves
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IntAtI (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s) * y ∈ RInt F E

def UnitAtI (P : HeightOneSpectrum (𝓞 E)) (y : (AfE F E)ˣ) : Prop := IntAtI P (y : AfE F E) ∧ IntAtI P ((y⁻¹ : (AfE F E)ˣ) : AfE F E)

def CongOneAtI (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ z ∈ P.asIdeal.map (toRInt F E),
    Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s) * (y - 1) = (z : AfE F E)

end Defs

def HilbertNinetyDeterminant : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n]
    (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), g ∈ UAd hc n →
      ∃ x : (AfE F E)ˣ, h90 hc.sig x = Matrix.GeneralLinearGroup.det g

def DetAtP : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n]
    (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), g ∈ UAd hc n →
      (∀ P : HeightOneSpectrum (𝓞 E), ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (decoOf ST SG g).1.N ↔ z ∈ stdAt E n P) ∧
      (∀ (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n),
        (∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (decoOf ST SG g).1.N ↔ z ∈ stdAt E n P) →
        UnitAtI P (Matrix.GeneralLinearGroup.det g * (ratId F E (LinearEquiv.det f))⁻¹)) ∧
      ∀ w : SG, CongOneAtI w.1
        ((Matrix.GeneralLinearGroup.det g * (ratId F E (LinearEquiv.det ((decoOf ST SG g).1.liftFr w)))⁻¹ : (AfE F E)ˣ) : AfE F E)

def CharFactor : Prop :=
  ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field L]
    (hc : CMData F E) (ξ : Chr F E L) (S : Finset (HeightOneSpectrum (𝓞 E))) (sel : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    (c : HeightOneSpectrum (𝓞 E) → Lˣ) (χ : ∀ P : HeightOneSpectrum (𝓞 E), (𝓞 E ⧸ P.asIdeal)ˣ →* Lˣ)
    (k : HeightOneSpectrum (𝓞 E) → Lˣ) (a : HeightOneSpectrum (𝓞 E) → Eˣ) (x : (AfE F E)ˣ),
    (∀ v, (sel v).asIdeal.under (𝓞 F) = v.asIdeal) →
    (∀ P ∈ S, ∃ P' : HeightOneSpectrum (𝓞 E), P' ≠ P ∧ P'.asIdeal.under (𝓞 F) = P.asIdeal.under (𝓞 F) ∧ P' ∉ S) →
    (∀ P ∈ S, ChainCounts.UnifAt P) →
    (h90 hc.sig).ker ≤ ξ.ker →
    (∀ y ∈ intU F E, (∀ P ∈ S, ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal →
      Units.map (Formalism.UG.prV (E := E) v).toMonoidHom y = 1) → ξ y = 1) →
    (∀ P : HeightOneSpectrum (𝓞 E), (¬ ∃ P' ∈ S, P'.asIdeal.under (𝓞 F) = P.asIdeal.under (𝓞 F)) → IsUnifVal ξ P (c P)) →
    (∀ P ∈ S, ∀ v : HeightOneSpectrum (𝓞 F), P.asIdeal.under (𝓞 F) = v.asIdeal → wildAt E v ≤ ξ.ker) →
    (∀ P ∈ S, IsResChar ξ P (χ P)) →
    (∀ P ∈ S, IsQValC ξ P (k P)) →
    {P : HeightOneSpectrum (𝓞 E) | ordE P (a P : E) ≠ 0}.Finite →
    (∀ P : HeightOneSpectrum (𝓞 E), UnitAtI P (h90 hc.sig x * (ratId F E (a P))⁻¹)) →
    (∀ P ∈ S, CongOneAtI P ((h90 hc.sig x * (ratId F E (a P))⁻¹ : (AfE F E)ˣ) : AfE F E)) →
    (((ξ x)⁻¹ : Lˣ) : L) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        open Classical in
        if ∃ P ∈ S, P.asIdeal.under (𝓞 F) = v.asIdeal then (1 : L) else (((c (sel v))⁻¹ ^ ordE (sel v) (a (sel v) : E) : Lˣ) : L)) *
      ∏ P ∈ S, LocE.locChar (qOf P) (((k P)⁻¹ : Lˣ) : L) (χ P)⁻¹ (a P : E)

end DetChrL

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ExistsYOfOfMemYbSet
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section YA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.yOfAt (d : Deco E n ST SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) (w : SG) (z : Sp E n) : Prop :=
  (qOf w.1 : E) • z ∈ d.at w.1 ∧ d.be w ((qOf w.1 : E) • z) = v w

theorem Deco.yOfAt_iff {d : Deco E n ST SG} {w : SG} {f : Sp E n ≃ₗ[E] Sp E n} (hf : d.IsLift w f)
    (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) (z : Sp E n) :
    d.yOfAt v w z ↔ ∀ i : Fin n, IntAt w.1 ((qOf w.1 : E) * f.symm z i) ∧ redP w.1 ((qOf w.1 : E) * f.symm z i) = v w i := by
  have e : (qOf w.1 : E) • z = f ((qOf w.1 : E) • f.symm z) := by rw [map_smul, LinearEquiv.apply_symm_apply]
  unfold Deco.yOfAt
  rw [e, hf.1, ciMem_stdAt]
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨h1 i, ?_⟩
    rw [hf.2 _ ((ciMem_stdAt _ _).2 h1)] at h2
    exact congrFun h2 i
  · intro h
    have h1 : ∀ i, IntAt w.1 (((qOf w.1 : E) • f.symm z) i) := fun i => (h i).1
    refine ⟨h1, ?_⟩
    rw [hf.2 _ ((ciMem_stdAt _ _).2 h1)]
    funext i
    exact (h i).2

theorem Deco.yOfAt_sub_iff {d : Deco E n ST SG} {w : SG} (hl : d.HasLift w) (hq2 : ((qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2)
    {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal} {z z' : Sp E n} (hz : d.yOfAt v w z) : d.yOfAt v w z' ↔ z' - z ∈ d.at w.1 := by
  obtain ⟨f, hf⟩ := hl
  have hq := ciQ_mem w.1
  have hq0 : ((qOf w.1 : ℕ) : E) ≠ 0 := ciQ_ne_zero hq2
  rw [Deco.yOfAt_iff hf] at hz ⊢
  have e : z' - z = f (f.symm z' - f.symm z) := by
    rw [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e, hf.1, ciMem_stdAt]
  constructor
  · intro h i
    have h1 := ciIntAt_sub (h i).1 (hz i).1
    have h2 : redP w.1 ((qOf w.1 : E) * f.symm z' i - (qOf w.1 : E) * f.symm z i) = 0 := by
      rw [redP_sub (h i).1 (hz i).1, (h i).2, (hz i).2, sub_self]
    have h3 := ciIntAt_div hq hq2 h1 h2
    have e2 : ((qOf w.1 : E) * f.symm z' i - (qOf w.1 : E) * f.symm z i) / (qOf w.1 : E) = f.symm z' i - f.symm z i := by
      field_simp
    rw [e2] at h3
    exact h3
  · intro h i
    have h' : IntAt w.1 (f.symm z' i - f.symm z i) := h i
    have e2 : (qOf w.1 : E) * f.symm z' i = (qOf w.1 : E) * f.symm z i + (qOf w.1 : E) * (f.symm z' i - f.symm z i) := by ring
    rw [e2]
    exact ⟨(ciIntAt_add_iff ((ciIntAt_q (q := qOf w.1)).mul h')).2 (hz i).1, by rw [redP_add_natCast_mul hq h']; exact (hz i).2⟩

theorem Deco.yOf_eq_of_mem {d : Deco E n ST SG} (hl : ∀ w, d.HasLift w) (hq2 : ∀ w : SG, ((qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2)
    {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal} {z : Sp E n} (hz : z ∈ d.yOf v) : d.yOf v = {z' | ∀ w : SG, z' - z ∈ d.at w.1} := by
  ext z'
  exact forall_congr' fun w => Deco.yOfAt_sub_iff (hl w) (hq2 w) (hz w)

theorem Deco.Ok.exists_beV {d : Deco E n ST SG} (hd : d.Ok) (c : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) :
    ∃ x ∈ d.N, ∀ w, d.be w x = c w := by
  classical
  choose x hx hxc using fun w : SG => hd.be_surj w (c w)
  have hcop : Pairwise fun w w' : SG => IsCoprime w.1.asIdeal w'.1.asIdeal := fun w w' hne => by
    show IsCoprime w.1.asIdeal w'.1.asIdeal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne w.1.isMaximal w'.1.isMaximal fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  choose a ha using fun w₀ : SG => Ideal.exists_forall_sub_mem_ideal hcop fun w : SG => if w = w₀ then (1 : 𝓞 E) else 0
  refine ⟨∑ w₀ : SG, a w₀ • x w₀, Submodule.sum_mem _ fun w₀ _ => Submodule.smul_mem _ _ (hx w₀), fun w => ?_⟩
  rw [hd.be_sum w _ _ fun w₀ _ => le_locP w.1 d.N (Submodule.smul_mem _ _ (hx w₀)), Finset.sum_eq_single w]
  · rw [hd.be_smul w _ _ (le_locP w.1 d.N (hx w)), hxc]
    have h1 := ha w w
    rw [if_pos rfl] at h1
    rw [(Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 h1, map_one, one_smul]
  · intro w₀ _ hne
    rw [hd.be_smul w _ _ (le_locP w.1 d.N (hx w₀))]
    have h1 := ha w₀ w
    rw [if_neg (Ne.symm hne), sub_zero] at h1
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h1, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem Deco.Ok.yOf_nonempty {d : Deco E n ST SG} (hd : d.Ok) (G : ℕ) (hG0 : G ≠ 0) (Gw : SG → ℕ) (hG : ∀ w, Gw w * qOf w.1 = G)
    (hGw : ∀ w : SG, ((Gw w : ℕ) : 𝓞 E) ∉ w.1.asIdeal) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) : ∃ y, y ∈ d.yOf v := by
  obtain ⟨x, hx, hxc⟩ := hd.exists_beV fun w => Ideal.Quotient.mk w.1.asIdeal ((Gw w : ℕ) : 𝓞 E) • v w
  refine ⟨(G : E)⁻¹ • x, fun w => ?_⟩
  have hGE : (G : E) ≠ 0 := by exact_mod_cast hG0
  have e : ((Gw w : ℕ) : 𝓞 E) • ((qOf w.1 : E) • ((G : E)⁻¹ • x)) = x := by
    rw [← algebraMap_smul E (((Gw w : ℕ) : 𝓞 E)), map_natCast, smul_smul, smul_smul, ← Nat.cast_mul, hG w, mul_inv_cancel₀ hGE, one_smul]
  have hmem : (qOf w.1 : E) • ((G : E)⁻¹ • x) ∈ d.at w.1 := (mem_locP w.1 d.N _).2 ⟨_, hGw w, by rw [e]; exact hx⟩
  refine ⟨hmem, ?_⟩
  have h1 := hd.be_smul w ((Gw w : ℕ) : 𝓞 E) _ hmem
  rw [e, hxc w] at h1
  funext i
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_left_cancel₀ (mk_ne_zero (hGw w)) h2).symm

end YA

section YB

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

variable {sel mu} in
theorem pc_rowSG (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  classical
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · exact absurd (hQ ▸ h : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 X.E)))) (Finset.notMem_empty _)

variable {sel mu cst} in
open Classical in

theorem pc_mem_locLat_zero (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : Sp X.E n) :
    v ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) ↔ ∀ w : Pr.vGs, v ∈ localization₂ w.1.asIdeal N := by
  classical
  rw [mem_locLat]
  constructor
  · intro h w
    have h1 := h ⟨w.1, Finset.mem_union_left _ w.2⟩
    rw [if_pos w.2, zpow_zero, inv_one, one_smul] at h1
    exact h1
  · intro h P
    rw [if_pos (hQ P), zpow_zero, inv_one, one_smul]
    exact h ⟨P.1, hQ P⟩

theorem pc_G_notMem (hPr : Pr.Ok) {i j : Fin 2} (hij : i ≠ j) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g j : ℕ) : 𝓞 X.E) ∉ w.asIdeal := by
  intro h
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
    rw [← ciQOf_eq hPr hw]
    exact ciQ_mem w
  have hne : Pr.g i ≠ Pr.g j := by
    intro e
    apply hPr.g_ne
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact e | exact e.symm
  have hc : Nat.Coprime (Pr.g i) (Pr.g j) := (Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
  have h2 : ((a : ℤ) : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) + ((b : ℤ) : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 X.E) hab
    push_cast at this
    exact this
  exact one_notMem w (h2 ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h))

theorem yOf_nonempty (hPr : Pr.Ok) {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} {d : Deco X.E n ST Pr.vGs} (hd : d.Ok)
    (v : ∀ w : Pr.vGs, Fin n → 𝓞 X.E ⧸ w.1.asIdeal) : ∃ y, y ∈ d.yOf v := by
  classical
  refine hd.yOf_nonempty (Pr.g 0 * Pr.g 1) (Nat.mul_ne_zero (hPr.g_prime 0).ne_zero (hPr.g_prime 1).ne_zero)
    (fun w => if w.1 ∈ Pr.vG 0 then Pr.g 1 else Pr.g 0) (fun w => ?_) (fun w => ?_) v
  · by_cases h0 : w.1 ∈ Pr.vG 0
    · simp only [if_pos h0]
      rw [ciQOf_eq hPr h0, mul_comm]
    · have h1 : w.1 ∈ Pr.vG 1 := (Finset.mem_union.1 w.2).resolve_left h0
      simp only [if_neg h0]
      rw [ciQOf_eq hPr h1]
  · by_cases h0 : w.1 ∈ Pr.vG 0
    · simp only [if_pos h0]
      exact pc_G_notMem hPr (by decide) h0
    · have h1 : w.1 ∈ Pr.vG 1 := (Finset.mem_union.1 w.2).resolve_left h0
      simp only [if_neg h0]
      exact pc_G_notMem hPr (by decide) h1

theorem yOf_mem_ybSet (hX : X.Ok) (hPr : Pr.Ok) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) {n : ℕ}
    {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST Pr.vGs) (v : ∀ w : Pr.vGs, Fin n → 𝓞 X.E ⧸ w.1.asIdeal) :
    d.1.yOf v ∈ ybSet sel mu cst d.1.N := by
  classical
  obtain ⟨y, hy⟩ := yOf_nonempty hPr d.2 v
  refine ⟨y, ?_, ?_⟩
  · rw [mem_locLat]
    intro P
    rw [if_pos (hQ P), _root_.zpow_neg, zpow_one, inv_inv]
    exact (hy ⟨P.1, hQ P⟩).1
  · rw [Deco.yOf_eq_of_mem (fun w => d.2.hasLift w) (fun w => ciQ_notMem_sq hX hPr w.2) hy]
    ext z
    exact (pc_mem_locLat_zero (cst := cst) hQ d.1.N (z - y)).symm

end YB

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.OcbBEntEntB
section
noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

def ocbBEnt {E : Type} [Field E] {N' N : ℕ} (n' n q : ℕ) (y : HomE E N' N) (l s : ℕ) : E :=
  Loc.atN (y (Loc.eN E N' s)) l * (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)

theorem ocbBEnt_entB {E : Type} [Field E] [NumberField E] {N' N : ℕ} (q k₀ c' n' c n : ℕ) (y : HomE E N' N) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) y p p' = ocbBEnt n' n q y (LocE.fIdx k₀ c n p) (LocE.fIdx k₀ c' n' p') := rfl

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RecChainYKmap
section
open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col.Sc

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker Formalism.L2.Col

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev SecY (u : Pr.Word) (m2 : ℕ) : Type := ∀ j b, ((Formalism.L2.Col.chFY W sel mu cst L u m2 j).mem b).Sec

@[reducible] def chFY (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) (j : ℕ) : GFamS X.K :=
  { toGFam := Formalism.L2.Col.chFY W sel mu cst L u m2 j, sec := sec j }

variable {W sel mu cst L}

def ptYc {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} {j : ℕ} (c : (chFY W sel mu cst L u m2 sec j).Cl) : ChPt (R := R) sel mu u j :=
  (((chFY W sel mu cst L u m2 sec j).sec c.1).rep c.2).1.1

def ybY {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} {j : ℕ} (c : (chFY W sel mu cst L u m2 sec j).Cl) : Set (Sp X.E (R.N j)) :=
  (((chFY W sel mu cst L u m2 sec j).sec c.1).rep c.2).1.2

def XiY {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl)
    (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  if i < m2 then XiEntry Ch sel mu cst L i c.1 c'.1 (ptYc c) (ptYc c') x
  else if i = m2 then XiCpl1 Ch sel mu cst L i c.1 (ptYc c) (ptYc c') (ybY c') x
  else if i = m2 + 1 then XiTop Ch sel mu cst i (ptYc c) (ybY c) (ptYc c') x
  else 0

def thY (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl) :
    VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ :=
  Am.thDat (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (ptYc c).deco.1.N (ptYc c').deco.1.N (XiY Ch i c c')

def kerYc (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl) :
    VV X.K (W.lamTrue u i) →ₗ[X.K] VV X.K (W.lamTrue u (i + 1)) :=
  kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    (ptYc c).deco.1.N (frsF sel mu (ptYc c)) (ptYc c').deco.1.N (frsF sel mu (ptYc c')) (XiY Ch i c c')

def rhoY (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c : (chFY W sel mu cst L u m2 sec i).Cl) : ℂ :=
  σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c).deco.1.N (frsF sel mu (ptYc c))) *
    (Am.chiF (R.N i) (R.N (i + 1)) (ptYc c).deco.1.N (stdLat X.E (R.N (i + 1))))⁻¹

def rhoY' (σ₀ : X.K →+* ℂ) (Am : Amb X) {u : Pr.Word} {m2 : ℕ} {sec : SecY W sel mu cst L u m2} (i : ℕ) (c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl) : ℂ :=
  (σ₀ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) (ptYc c').deco.1.N (frsF sel mu (ptYc c'))))⁻¹ *
    (Am.chiF (R.N i) (R.N (i + 1)) (stdLat X.E (R.N i)) (ptYc c').deco.1.N)⁻¹

def RhoYUnit (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) : Prop :=
  (∀ i, i < R.m → ∀ c : (chFY W sel mu cst L u m2 sec i).Cl, ‖rhoY Ch σ₀ Am i c‖ = 1) ∧
    ∀ i, i < R.m → ∀ c' : (chFY W sel mu cst L u m2 sec (i + 1)).Cl, ‖rhoY' Ch σ₀ Am i c'‖ = 1

def ChainArgF.ofChKer (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2 sec) :
    ChainArgF R (fun i => (chFY W sel mu cst L u m2 sec i).toGFam) σ₀ where
  rhoDet := rhoY Ch σ₀ Am
  rhoDet' := rhoY' Ch σ₀ Am
  rho_norm := hU.1
  rho'_norm := hU.2
  unf i c c' := unfTh σ₀ Am.cD (thY Ch Am i c c')

def recChainY (σ₀ : X.K →+* ℂ) (Am : Amb X) (u : Pr.Word) (m2 : ℕ) (sec : SecY W sel mu cst L u m2) (hU : RhoYUnit (W := W) (cst := cst) (L := L) Ch σ₀ Am u m2 sec)
    (hF : ∀ j, (chFY W sel mu cst L u m2 sec j).Ok) (D : ℕ) (hD : 0 < D)
    (hdvd : ∀ j, j ≤ R.m → ∀ c : (chFY W sel mu cst L u m2 sec j).Cl, Nat.card (FamStabS (chFY W sel mu cst L u m2 sec j) c) ∣ D) :
    ColumnChain R X.Tau (W.hc u) :=
  recChainFS (W.hc u) (chFY W sel mu cst L u m2 sec) hF σ₀ D hD hdvd (ChainArgF.ofChKer Ch σ₀ Am u m2 sec hU)

variable {Ch}

end Charts

end Formalism.L2.Col.Sc
end
end

