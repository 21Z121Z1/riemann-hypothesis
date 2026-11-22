import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePFBMapSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.MapFB

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}

def mpt {n : ℕ} (a : Pt R n d) : Pt S n d := fun i => MvPowerSeries.map φ (a i)

private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : MvPowerSeries.map φ (ev a f) = ev (fun j => mpt φ (a j)) (MvPowerSeries.map φ f) := by
  unfold ev
  exact MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2)) f

theorem map_ev1 {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS R 1 d) :
    MvPowerSeries.map φ (ev ![a] f) = ev ![mpt φ a] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a] (by intro j i; fin_cases j; simp [ha]) f]
  congr 1
  funext j
  fin_cases j
  rfl

theorem map_ev2 {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mpt φ a, mpt φ b] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem map_ev3 {n : ℕ} (a b c : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0) (f : PS R 3 d) :
    MvPowerSeries.map φ (ev ![a, b, c] f) = ev ![mpt φ a, mpt φ b, mpt φ c] (MvPowerSeries.map φ f) := by
  rw [map_ev φ ![a, b, c] (by intro j i; fin_cases j <;> simp [ha, hb, hc]) f]
  congr 1
  funext j
  fin_cases j <;> rfl

omit [CommRing S] in
theorem cc_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 := by
  unfold ev
  exact (cc_subst_lemma (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f).trans hf

omit [CommRing S] in
@[simp] theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]

omit [CommRing S] in
@[simp] theorem cc_addOf {n : ℕ} (F : Fin d → PS R 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin d) :
    constantCoeff (addOf F a b i) = 0 := cc_ev ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) (F i) (hF i)

omit [CommRing S] in
@[simp] theorem cc_comp1 {n : ℕ} (ψ : Pt R 1 d) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) :
    constantCoeff (comp1 ψ a i) = 0 := cc_ev ![a] (by intro j i; fin_cases j; simp [ha]) (ψ i) (hψ i)

omit [CommRing S] in
theorem zc_zero {n : ℕ} : ∀ i : Fin d, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp

@[simp] theorem mpt_pt {n : ℕ} (j : Fin n) : mpt φ (pt R d j) = pt S d j := by
  funext i
  simp [mpt, pt]

@[simp] theorem mpt_zero {n : ℕ} : mpt φ (0 : Pt R n d) = 0 := by
  funext i
  simp [mpt]

theorem mpt_addOf {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    mpt φ (addOf F a b) = addOf (fun i => MvPowerSeries.map φ (F i)) (mpt φ a) (mpt φ b) := by
  funext i
  exact map_ev2 φ a b ha hb (F i)

theorem mpt_comp1 {n : ℕ} (ψ : Pt R 1 d) (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mpt φ (comp1 ψ a) = comp1 (mpt φ ψ) (mpt φ a) := by
  funext i
  exact map_ev1 φ a ha (ψ i)

def mapLaw (G : FGLaw R d) : FGLaw S d where
  F := fun i => MvPowerSeries.map φ (G.F i)
  const := by intro i; simp [constantCoeff_map, G.const]
  unit := by
    intro i
    have h := congrArg (MvPowerSeries.map φ) (G.unit i)
    rw [map_ev2 φ _ _ (by simp) (by simp), map_X, mpt_zero, mpt_pt] at h
    exact h
  comm := by
    intro i
    have h := congrArg (MvPowerSeries.map φ) (G.comm i)
    simpa [map_ev2] using h
  assoc := by
    intro i
    have h := congrArg (MvPowerSeries.map φ) (G.assoc i)
    change MvPowerSeries.map φ (ev ![addOf G.F (pt R d 0) (pt R d 1), pt R d 2] (G.F i)) =
      MvPowerSeries.map φ (ev ![pt R d 0, addOf G.F (pt R d 1) (pt R d 2)] (G.F i)) at h
    change ev ![addOf (fun l => MvPowerSeries.map φ (G.F l)) (pt S d 0) (pt S d 1), pt S d 2]
        (MvPowerSeries.map φ (G.F i)) =
      ev ![pt S d 0, addOf (fun l => MvPowerSeries.map φ (G.F l)) (pt S d 1) (pt S d 2)]
        (MvPowerSeries.map φ (G.F i))
    simpa [map_ev2, mpt_addOf, G.const] using h

def mapAct {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : OAct O (mapLaw φ G) where
  act := fun a => mpt φ (A.act a)
  const := by intro a i; simp [mpt, constantCoeff_map, A.const]
  hom := by
    intro a
    have h := congrArg (mpt φ) (A.hom a)
    simpa [FGLaw.add, mapLaw, mpt_comp1, mpt_addOf, G.const, A.const] using h
  add_act := by
    intro a b
    have h := congrArg (mpt φ) (A.add_act a b)
    simpa [FGLaw.add, mapLaw, mpt_addOf, A.const] using h
  mul_act := by
    intro a b
    have h := congrArg (mpt φ) (A.mul_act a b)
    simpa [mpt_comp1, A.const] using h
  one_act := by
    have h := congrArg (mpt φ) A.one_act
    simpa using h

def mapFB {O : Type} [CommRing O] [StarRing O] (B : FB R d O) : FB S d O where
  G := mapLaw φ B.G
  A := mapAct φ B.A
  ph1 := MvPowerSeries.map φ B.ph1
  ph2 := MvPowerSeries.map φ B.ph2
  sy := MvPowerSeries.map φ B.sy
  ad := fun a => MvPowerSeries.map φ (B.ad a)
  cocycleLeft_zero_fst := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleLeft_zero_fst
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleLeft_zero_snd := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleLeft_zero_snd
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleLeft_zero_thd := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleLeft_zero_thd
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleRight_zero_fst := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleRight_zero_fst
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleRight_zero_snd := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleRight_zero_snd
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleRight_zero_thd := by
    have h := congrArg (MvPowerSeries.map φ) B.cocycleRight_zero_thd
    rw [map_ev3 φ _ _ _ (by simp) (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  symmetry_zero_fst := by
    have h := congrArg (MvPowerSeries.map φ) B.symmetry_zero_fst
    rw [map_ev2 φ _ _ (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  symmetry_zero_snd := by
    have h := congrArg (MvPowerSeries.map φ) B.symmetry_zero_snd
    rw [map_ev2 φ _ _ (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  cocycleLeft_assoc := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.cocycleLeft_assoc
  cocycleLeft_comm := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.cocycleLeft_comm
  cocycleRight_assoc := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.cocycleRight_assoc
  cocycleRight_comm := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.cocycleRight_comm
  interchange := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.interchange
  sy_inv := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.sy_inv
  sy_law := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.sy_law
  ad_one := by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) B.ad_one
  adjoint_zero_fst := fun a => by
    have h := congrArg (MvPowerSeries.map φ) (B.adjoint_zero_fst a)
    rw [map_ev2 φ _ _ (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  adjoint_zero_snd := fun a => by
    have h := congrArg (MvPowerSeries.map φ) (B.adjoint_zero_snd a)
    rw [map_ev2 φ _ _ (by simp) (by simp), map_one] at h
    simpa only [mpt_zero, mpt_pt] using h
  adjoint_compat_left := fun a => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.adjoint_compat_left a)
  adjoint_compat_right := fun a => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.adjoint_compat_right a)
  ad_sy := fun a => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.ad_sy a)
  ad_mul := fun a b => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.ad_mul a b)
  ad_add := fun a b => by simpa [FGLaw.add, mapLaw, mapAct, map_ev1, map_ev2, map_ev3, mpt_addOf, mpt_comp1, FGLaw.const, OAct.const, zc_zero] using congrArg (MvPowerSeries.map φ) (B.ad_add a b)

end Formalism.L2.FormalSeriesBounds.MapFB

namespace Formalism.L2.FormalSeriesBounds

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

structure LabS (E : Type) [Field E] (C : Type) (Orb : Type) (d : ℕ) where
  tau : Orb → ZMod d → (E →+* ℂ)
  hd : ZMod d
  gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Orb → Fin 2 → ZMod d → Prop

abbrev LabS.II {Orb : Type} {d : ℕ} (lab : LabS E C Orb d) (Dw : Datum H) (o : Orb) : Type :=
  Σ a : ZMod d, Fin (Dw.mult (lab.tau o a))

section Pairs

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

def selfLieBasisVector (C3 : IntChart T io y) (ι : T.Fr →+* C) (lab : LabS E C Orb d) (o : Orb) (x : lab.II Dw o) :
    Fin (chD C3.ch) → C := fun i => ι (chartUnitVectors C3 ⟨lab.tau o x.1, x.2⟩ i)

structure LabSArith (V : VF C) (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (lab : LabS E C Orb d) : Prop where
  inj : Function.Injective fun x : Orb × ZMod d => lab.tau x.1 x.2
  hd_ne : lab.hd ≠ 0
  hd_two : lab.hd + lab.hd = 0
  conj : ∀ o a, ComplexEmbedding.conjugate (lab.tau o a) = lab.tau o (a + lab.hd)
  frob : ∀ o a x, V.MM (emA3 io ι (lab.tau o (a + 1)) x - emA3 io ι (lab.tau o a) x ^ V.l)
  sep : ∀ x x' : Orb × ZMod d, x ≠ x' →
    ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2) a - emA3 io ι (lab.tau x'.1 x'.2) a) = 0
  unr : ∀ o, ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (lab.tau o a) ε - 1)) ∧
    ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (lab.tau o a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y
  gm_lim : ∀ o (N : ℕ), ∃ M : Matrix (Fin 2) (Fin 2) (𝓞 E), ∀ a r s,
    V.Ge N (lab.gm o a r s - emA3 io ι (lab.tau o a) (M r s))
  gm_hyp : ∀ o a (s s' : Fin 2), ∑ r, lab.gm o (a + lab.hd) r s * lab.gm o a r s' = if s = s' then 0 else 1

structure LabSGeo (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : LabS E C Orb d) :
    Prop where
  em_int : ∀ o a x, V.Ge 0 (emA3 io ι (lab.tau o a) x)
  em_conj : ∀ o a x, emA3 io ι (lab.tau o a) (star x) = emA3 io ι (lab.tau o (a + lab.hd)) x
  e_int : ∀ o x i, V.Ge 0 (selfLieBasisVector C3 ι lab o x i)
  e_eig : ∀ o (x : lab.II Dw o) a, linAct (Y.B.A.act a) (selfLieBasisVector C3 ι lab o x) =
    emA3 io ι (lab.tau o x.1) a • selfLieBasisVector C3 ι lab o x
  e_sat : ∀ o, ∃ w : Fin (chD C3.ch) → lab.II Dw o → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o, ∑ x, selfLieBasisVector C3 ι lab o q x * w x q' = if q = q' then 1 else 0
  e_full : ∀ o a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o a) x • v) →
    ∃ b : lab.II Dw o → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • selfLieBasisVector C3 ι lab o q

def selfOfLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (o : Orb) : SelfData Y d (lab.II Dw o) where
  em := fun a => emA3 io ι (lab.tau o a)
  em_int := hg.em_int o
  em_frob := ha.frob o
  em_sep := fun a a' h => ha.sep (o, a) (o, a') (fun e => h (Prod.mk.inj e).2)
  em_unr := ha.unr o
  hd := lab.hd
  hd_ne := ha.hd_ne
  hd_two := ha.hd_two
  em_conj := hg.em_conj o
  e := selfLieBasisVector C3 ι lab o
  ty0 := fun x => x.1
  e_int := hg.e_int o
  e_eig := hg.e_eig o
  e_sat := by
    obtain ⟨w, h1, h2⟩ := hg.e_sat o
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  e_full := hg.e_full o
  gm := lab.gm o
  gm_lim := ha.gm_lim o
  gm_hyp := ha.gm_hyp o
  n := lab.n
  j := lab.j
  j' := lab.j'
  big := lab.big o

theorem selfSep_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) : SelfSep Y (selfOfLab ha hg) := by
  intro x x' hne
  exact ha.sep x x' hne

def LabS.RankOK (lab : LabS E C Orb d) (Dw : Datum H) : Prop :=
  ∀ o, (∀ g a, lab.big o (1 - g) a ↔ ¬ lab.big o g a) ∧
    (∀ a, lab.big o 0 a → Dw.mult (lab.tau o a) = lab.n + lab.j) ∧
    (∀ a, ¬ lab.big o 0 a → Dw.mult (lab.tau o a) = lab.j') ∧
    (∀ a, lab.big o 1 a → Dw.mult (lab.tau o (a - lab.hd)) = lab.n + lab.j) ∧
    (∀ a, ¬ lab.big o 1 a → Dw.mult (lab.tau o (a - lab.hd)) = lab.j')

theorem card_sigma_shift (m : ZMod d → ℕ) (h a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a).card = m (a - h) := by
  have e1 : (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 + h = a) =
      (Finset.univ.filter fun b : ZMod d => b + h = a).sigma fun b => Finset.univ := by
    ext ⟨b, i⟩
    simp
  have e2 : (Finset.univ.filter fun b : ZMod d => b + h = a) = {a - h} := by
    ext b
    simp [eq_sub_iff_add_eq]
  rw [e1, Finset.card_sigma, e2, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin]

theorem rankHyp_ofLabS {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.rawSelf (selfOfLab ha hg o)).RankHyp where
  big_compl := (hr o).1
  rk_big := fun g a hb => by
    fin_cases g
    · exact (card_sigma_fst (fun a => Dw.mult (lab.tau o a)) a).trans ((hr o).2.1 a hb)
    · exact (card_sigma_shift (fun a => Dw.mult (lab.tau o a)) lab.hd a).trans ((hr o).2.2.2.1 a hb)
  rk_small := fun g a hb => by
    fin_cases g
    · exact (card_sigma_fst (fun a => Dw.mult (lab.tau o a)) a).trans ((hr o).2.2.1 a hb)
    · exact (card_sigma_shift (fun a => Dw.mult (lab.tau o a)) lab.hd a).trans ((hr o).2.2.2.2 a hb)

end Pairs

section Named

variable (Xo c)

def GmExSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → V.l ≠ 2 →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (tau : Orb → ZMod d → (E →+* ℂ)) (hd : ZMod d), hd ≠ 0 → hd + hd = 0 →
    (∀ o a, ComplexEmbedding.conjugate (tau o a) = tau o (a + hd)) →
    (∀ o a x, V.MM (emA3 io ι (tau o (a + 1)) x - emA3 io ι (tau o a) x ^ V.l)) →
    (∀ x x' : Orb × ZMod d, x ≠ x' → ∃ a : 𝓞 E, V.v (emA3 io ι (tau x.1 x.2) a - emA3 io ι (tau x'.1 x'.2) a) = 0) →
    ∃ gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C,
      (∀ o (N : ℕ), ∃ M : Matrix (Fin 2) (Fin 2) (𝓞 E), ∀ a r s, V.Ge N (gm o a r s - emA3 io ι (tau o a) (M r s))) ∧
      ∀ o a (s s' : Fin 2), ∑ r, gm o (a + hd) r s * gm o a r s' = if s = s' then 0 else 1

def LabSGeoSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d), LabSArith V io ι lab → LabSGeo C3 ι Y lab

def AllSelfConjugateCharts (Φ : ∀ (C : Type) [Field C] (_V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin 2 × Fin dd) → Prop) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : LabS E C Orb d) (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, Φ C V d (fun _ => lab.II Dw o) (chD C3.ch) (Y.rawSelf (selfOfLab ha hg o))

def RankMaximalSelfCharts : Prop := AllSelfConjugateCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition Hc

def CharacterHypothesisSelfCharts : Prop := AllSelfConjugateCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.CHSt Hc

end Named

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem hypotheses_of_self_labelling (hCart : CartSelfSt) (hAx : AxesSelfSt) (hG0 : GermZeroSelfConjugate) (hC : CEqSelfSt) (hR1 : IndependenceBoundSelfConjugate)
    (hR2 : RankMaximalSelfCharts Xo c) (hCH : CharacterHypothesisSelfCharts Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.rawSelf (selfOfLab ha hg o)).Hyps V where
  charZero := inferInstance
  algClosed := Y.algClosed
  l_odd := Y.l_odd
  k_unit := Y.k_unit
  cartH := hCart C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
  rank := rankHyp_ofLabS ha hg hr o
  axes := hAx C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
  G0 := hG0 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) _
  CEq := hC C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
  R1 := hR1 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
    (hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _)
  R2 := hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _
  CH := hCH hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _

def selfConjugateRowData (hCart : CartSelfSt) (hAx : AxesSelfSt) (hG0 : GermZeroSelfConjugate) (hC : CEqSelfSt) (hR1 : IndependenceBoundSelfConjugate)
    (hR2 : RankMaximalSelfCharts Xo c) (hCH : CharacterHypothesisSelfCharts Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    RowData C V d (fun _ => lab.II Dw o) (JJ fun _ => lab.II Dw o) :=
  (Y.rawSelf (selfOfLab ha hg o)).rowData (hypotheses_of_self_labelling hCart hAx hG0 hC hR1 hR2 hCH hstar hι hY ha hg hr o)

theorem nuLocC_le_self [Fintype Orb] (hD : DescentSt Xo c) {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hv : ValEqSelfSt Y (selfOfLab ha hg) Hy (chartLetterSystem C3 V ι a) n)
    (N : ℕ) (pl : Fin N × Fin 2 ↪ Fin n)
    (P : MvPolynomial (LtN Dw n) C) (hP : P ∈ (chartLetterSystem C3 V ι a).FF n)
    (Po : ∀ o, MvPolynomial (Fin N × WV fun _ => lab.II Dw o) C)
    (hQ : IsImgS (fun o => Y.rawSelf (selfOfLab ha hg o)) pl ((chartLetterSystem C3 V ι a).cp n) ((chartLetterSystem C3 V ι a).uv n) P
      (∏ o, toAll o (Po o)))
    (kind : Orb → Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (hk : ∀ o, RowsOK ((Y.rawSelf (selfOfLab ha hg o)).rowData (Hy o)).G
      ((Y.rawSelf (selfOfLab ha hg o)).rowData (Hy o)).Alt (Po o) (kind o))
    (S : ∀ o g, Sys (((Y.rawSelf (selfOfLab ha hg o)).rowData (Hy o)).G g))
    (t : ∀ o (_ : Fin 2), lab.II Dw o → MvPowerSeries (lab.II Dw o) C) (ht : ∀ o g, (S o g).IsT (t o g))
    (gr : ∀ o, Fin N → MvPowerSeries (WV fun _ => lab.II Dw o) C) (hgr : ∀ o ρ, gr o ρ ∈ IntGerm V (t o)) :
    nuLocC C3 (eOf T V) k a n ≤
      (WithBot.some (∑ o, V.v (ValOf ((Y.rawSelf (selfOfLab ha hg o)).rowData (Hy o)).hL (Po o) (kind o) (gr o))) :
        WithBot (WithTop ℝ)) :=
  le_trans (hD T io y C3 C V ι hι k Y hY a n)
    (val_self (hs := selfSep_ofLab ha hg) (hv := hv) (N := N) (pl := pl) (P := P) (hP := hP) (Po := Po)
      (hQ := hQ) (kind := kind) (hk := hk) (S := S) (t := t) (ht := ht) (gr := gr) (hg := hgr))

end Top

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValBlocksCChart
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

section Gen

variable {d : ℕ} [NeZero d] (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

abbrev rdS (o : Orb) : RowData C V d (fun _ => I0 o) (JJ fun _ => I0 o) := (Y.rawSelf (p o)).rowData (H o)

def imgFamS {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : Set (∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

theorem valO_self (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : ValO (fun o => rdS Y p H o) N (imgFamS Y p Ls n pl) ν := by
  rintro Po ⟨P, hP, hQ⟩ kind hk S t ht gr hg
  have key := val_self (hs := hs) (hv := hv) (N := N) (pl := pl) (P := P) (hP := hP) (Po := Po) (hQ := hQ)
    (kind := kind) (hk := hk) (S := S) (t := t) (ht := ht) (gr := gr) (hg := hg)
  exact WithBot.coe_le_coe.1 (hν.trans key)

end Gen

section Two

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y 2 (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

theorem valBlocksC_chart (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (F : ∀ o, Flag (rdS Y p H o)) (nW : ℕ) (hn : nW ≤ 2 * N + 1)
    (gaC : Orb → ZMod 2 → ℕ → ℕ) (hM : BlockMembershipSelfConjugate (fun o => rdS Y p H o) N F (imgFamS Y p Ls n pl) gaC)
    (hA : ∀ o, (rdS Y p H o).Alt) (hj : ∀ o, (rdS Y p H o).j' < (rdS Y p H o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (rdS Y p H o).rkF 0 s) :
    ValBlocksC (fun o => rdS Y p H o) F nW gaC ν :=
  valBlocksC_G (hV := valO_self (hν := hν) (hs := hs) (hv := hv) (pl := pl)) (hJ := jetProd) (F := F) (nW := nW)
    (hn := hn) (gaC := gaC) (hM := hM) (hA := blkAdmC (F := F) (gaC := gaC) (hA := hA) (hj := hj) (hga := hga))

end Two

end Formalism.L2.FormalSeriesBounds.RF
end
end

