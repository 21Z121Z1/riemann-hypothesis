import Formalism.LocalToGlobal.CharacterGerms.Bundle0007
import Formalism.LocalToGlobal.CharacterGerms.RowTieVal
import Formalism.LocalToGlobal.CharacterGerms.Bundle0010

-- bundled from Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
  (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)

abbrev rd (o : Orb) : RowData C V d (I o) (JJ (I o)) := (Y.raw (p o)).rowData (H o)

def imgFam : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgO (fun o => Y.raw (p o)) (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

theorem valO_of (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p) (hv : ValEqPSt Y p H Ls n) :
    ValO (fun o => rd Y p H o) n (imgFam Y p Ls n) ν := by
  intro Po hPo kind hk S t ht gr hg
  obtain ⟨P, hP, hQ⟩ := hPo
  obtain ⟨f, hf, he⟩ := hv hs P hP Po hQ kind hk S t ht gr hg
  have hx := hν _ ⟨P, hP, f, hf, rfl⟩
  rw [he, map_prod_add] at hx
  exact hx

theorem lower_of_nuPlE (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x := by
  intro x hx
  have h1 : (ν : EReal) ≤ (WithBot.some x : WithBot (WithTop ℝ)) := hν.trans (biInf_le _ hx)
  exact WithBot.coe_le_coe.1 h1

variable (F : ∀ o, Flag (rd Y p H o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

def BlockMembershipChart : Prop := BlockMembership (fun o => rd Y p H o) n F (imgFam Y p Ls n) Z ga

def BlockAdmissibleChart : Prop := BlockAdmissible (fun o => rd Y p H o) F Z ga

theorem valBlocks_of (ν : ℝ) (hν : ∀ x ∈ Y.valSet Ls n, (ν : WithTop ℝ) ≤ x) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_G (valO_of Y p H Ls n ν hν hs hv) hJ F Z ga hM hA

theorem valBlocks_of_nuPlE (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : PairsSep Y p)
    (hv : ValEqPSt Y p H Ls n) (hJ : JetProdSt) (hM : BlockMembershipChart Y p H Ls n F Z ga) (hA : BlockAdmissibleChart Y p H F Z ga) :
    ValBlocks (fun o => rd Y p H o) F Z n ga ν :=
  valBlocks_of Y p H Ls n F Z ga ν (lower_of_nuPlE Y Ls n ν hν) hs hv hJ hM hA

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def VF.RR {C : Type} [Field C] (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def a3B (C3 : IntChart T io y) : FB T.Fr (chD C3.ch) (𝓞 E) := letI := io.toAlgebra; C3.ch.B

def a3h (C3 : IntChart T io y) : PS T.Fr 2 (chD C3.ch) := letI := io.toAlgebra; C3.ch.h

def chartUnitVectors (C3 : IntChart T io y) : Lt1 Dw → Fin (chD C3.ch) → T.Fr := letI := io.toAlgebra; C3.ch.uvec

def EmbOK (T : CDVR) (V : VF C) (ι : T.Fr →+* C) : Prop :=
  ∀ x : T.Fr, x ≠ 0 → V.v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((V.l : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)

def eOf (T : CDVR) (V : VF C) : ℕ := (vV T.V ((V.l : ℕ) : T.Fr)).toNat

structure IsBC (C3 : IntChart T io y) (ι : T.Fr →+* C) (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)) : Prop where
  F : ∀ j, Y.B.G.F j = MvPowerSeries.map ι ((a3B C3).G.F j)
  act : ∀ a j, Y.B.A.act a j = MvPowerSeries.map ι ((a3B C3).A.act a j)
  ph1 : Y.B.ph1 = MvPowerSeries.map ι (a3B C3).ph1
  ph2 : Y.B.ph2 = MvPowerSeries.map ι (a3B C3).ph2
  sy : Y.B.sy = MvPowerSeries.map ι (a3B C3).sy
  ad : ∀ a, Y.B.ad a = MvPowerSeries.map ι ((a3B C3).ad a)
  h : Y.h = MvPowerSeries.map ι (a3h C3)
  w0 : Y.w0 = H.w0
  k : Y.k = k

def chartLetterSystem (C3 : IntChart T io y) (V : VF C) (ι : T.Fr →+* C) (a : (E →+* ℂ) × ℕ → ℕ) : LetSys C (chD C3.ch) where
  ι := fun N => LtN Dw N
  fin := fun _ => inferInstance
  cp := fun _ ℓ => ℓ.2.2
  uv := fun _ ℓ i => ι (chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩ i)
  FF := fun N => HaO Dw.mult N C V.RR ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)

end Chart

structure Lab (E : Type) [Field E] (Orb : Type) (d : ℕ) where
  tau : Orb → Fin 2 → ZMod d → (E →+* ℂ)
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Orb → Fin 2 → ZMod d → Prop

abbrev Lab.II {Orb : Type} {d : ℕ} (lab : Lab E Orb d) (Dw : Datum H) (o : Orb) (g : Fin 2) : Type :=
  Σ a : ZMod d, Fin (Dw.mult (lab.tau o g a))

section Pairs

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

def emA3 (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (τ : E →+* ℂ) : 𝓞 E →+* C := (ι.comp io).comp (embK c τ)

def lieBasisVector (C3 : IntChart T io y) (ι : T.Fr →+* C) (lab : Lab E Orb d) (o : Orb) (g : Fin 2) (x : lab.II Dw o g) :
    Fin (chD C3.ch) → C := fun i => ι (chartUnitVectors C3 ⟨lab.tau o g x.1, x.2⟩ i)

structure LabArith (V : VF C) (io : c.F →+* T.Fr) (ι : T.Fr →+* C) (lab : Lab E Orb d) : Prop where
  inj : Function.Injective fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2
  conj : ∀ o a, lab.tau o 1 a = ComplexEmbedding.conjugate (lab.tau o 0 a)
  frob : ∀ o g a x, V.MM (emA3 io ι (lab.tau o g (a + 1)) x - emA3 io ι (lab.tau o g a) x ^ V.l)
  sep : ∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' →
    ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau x.1 x.2.1 x.2.2) a - emA3 io ι (lab.tau x'.1 x'.2.1 x'.2.2) a) = 0
  unr : ∀ o g, ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (lab.tau o g a) ε - 1)) ∧
    ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (lab.tau o g a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y

structure LabGeo (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : Lab E Orb d) :
    Prop where
  em_int : ∀ o g a x, V.Ge 0 (emA3 io ι (lab.tau o g a) x)
  em_conj : ∀ o a x, emA3 io ι (lab.tau o 1 a) x = emA3 io ι (lab.tau o 0 a) (star x)
  u_int : ∀ o g x i, V.Ge 0 (lieBasisVector C3 ι lab o g x i)
  u_eig : ∀ o g (x : lab.II Dw o g) a, linAct (Y.B.A.act a) (lieBasisVector C3 ι lab o g x) =
    emA3 io ι (lab.tau o g x.1) a • lieBasisVector C3 ι lab o g x
  u_sat : ∀ o g, ∃ w : Fin (chD C3.ch) → lab.II Dw o g → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o g, ∑ x, lieBasisVector C3 ι lab o g q x * w x q' = if q = q' then 1 else 0
  u_full : ∀ o g a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o g a) x • v) →
    ∃ b : lab.II Dw o g → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • lieBasisVector C3 ι lab o g q

def pairOfLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (o : Orb) : PairData Y d (lab.II Dw o) where
  em := fun g a => emA3 io ι (lab.tau o g a)
  em_int := hg.em_int o
  em_conj := hg.em_conj o
  em_frob := ha.frob o
  em_sep := fun p p' hp => ha.sep (o, p) (o, p') (fun h => hp (Prod.mk.inj h).2)
  em_unr := ha.unr o
  u := lieBasisVector C3 ι lab o
  ty := fun _ x => x.1
  u_int := hg.u_int o
  u_eig := hg.u_eig o
  u_sat := fun g => by
    obtain ⟨w, h1, h2⟩ := hg.u_sat o g
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  u_full := hg.u_full o
  n := lab.n
  j := lab.j
  j' := lab.j'
  big := lab.big o

theorem pairsSep_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) : PairsSep Y (pairOfLab ha hg) :=
  fun x x' h => ha.sep x x' h

end Pairs

section Named

variable (Xo c)

def BCExSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → IsAlgClosed C →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → V.l ≠ 2 →
    H.w0 + star H.w0 = 1 → ∀ k : ℕ, V.v (k : C) = 0 → ∃ Y : FBChart C V (𝓞 E) (chD C3.ch), IsBC C3 ι k Y

def HostTraceIdentity (H : Host E) : Prop := (∀ a : 𝓞 E, star a = H.bar a) → H.w0 + star H.w0 = 1

def DescentSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), nuLocC C3 (eOf T V) k a n ≤ Y.nuPlE (chartLetterSystem C3 V ι a) n

def LabGeoSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → LabGeo C3 ι Y lab

end Named

def Lab.RankOK {Orb : Type} {d : ℕ} (lab : Lab E Orb d) (Dw : Datum H) : Prop :=
  ∀ o, (∀ g a, lab.big o (1 - g) a ↔ ¬ lab.big o g a) ∧
    (∀ g a, lab.big o g a → Dw.mult (lab.tau o g a) = lab.n + lab.j) ∧
    (∀ g a, ¬ lab.big o g a → Dw.mult (lab.tau o g a) = lab.j')

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb] {d : ℕ} [NeZero d]

theorem nuLocC_le (hD : DescentSt Xo c) {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hv : ValEqPSt Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) n)
    (P : MvPolynomial (LtN Dw n) C) (hP : P ∈ (chartLetterSystem C3 V ι a).FF n)
    (Po : ∀ o, MvPolynomial (Fin n × WV (lab.II Dw o)) C)
    (hQ : IsImgO (fun o => Y.raw (pairOfLab ha hg o)) ((chartLetterSystem C3 V ι a).cp n) ((chartLetterSystem C3 V ι a).uv n) P
      (∏ o, toAll o (Po o)))
    (kind : Orb → Fin n → Option (Fin 2 × ZMod d × ZMod d))
    (hk : ∀ o, RowsOK ((Y.raw (pairOfLab ha hg o)).rowData (Hy o)).G ((Y.raw (pairOfLab ha hg o)).rowData (Hy o)).Alt
      (Po o) (kind o))
    (S : ∀ o g, Sys (((Y.raw (pairOfLab ha hg o)).rowData (Hy o)).G g))
    (t : ∀ o g, lab.II Dw o g → MvPowerSeries (lab.II Dw o g) C) (ht : ∀ o g, (S o g).IsT (t o g))
    (gr : ∀ o, Fin n → MvPowerSeries (WV (lab.II Dw o)) C) (hgr : ∀ o ρ, gr o ρ ∈ IntGerm V (t o)) :
    nuLocC C3 (eOf T V) k a n ≤
      (WithBot.some (∑ o, V.v (ValOf ((Y.raw (pairOfLab ha hg o)).rowData (Hy o)).hL (Po o) (kind o) (gr o))) :
        WithBot (WithTop ℝ)) := by
  have hsep : PairsSep Y (pairOfLab ha hg) := pairsSep_ofLab ha hg
  obtain ⟨f, hf, he⟩ := hv hsep P hP Po hQ kind hk S t ht gr hgr
  refine (hD T io y C3 C V ι hι k Y hY a n).trans ?_
  unfold FBChart.nuPlE
  refine (iInf₂_le (V.v (Y.nab (chartLetterSystem C3 V ι a) n f P)) ⟨P, hP, f, hf, rfl⟩).trans ?_
  rw [he, map_prod_add]
  exact le_rfl

end Top

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.NegMem
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem tyS_add {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) : tyS l (fun s => a s + b s) = tyS l a + tyS l b := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def AddCvSt (V : VF C) : Prop :=
  ∀ γ γ' : κ → PowerSeries C, IsCv V γ → IsCv V γ' →
    ∃ γ'' : κ → PowerSeries C, IsCv V γ'' ∧
      (∀ i, alongCv γ'' (X.lg i) = alongCv γ (X.lg i) + alongCv γ' (X.lg i)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) →
        PowerSeries.constantCoeff (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)) = 0 ∧
        ∀ n, V.Ge 0 (PowerSeries.coeff n (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)))

private theorem ge_add_lemma (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.Ge 0 (a + b) := by
  unfold VF.Ge at *
  exact le_trans (le_min ha hb) (V.v.map_add a b)

theorem add_mem (V : VF C) (g : Fin 2) (hA : X.AddCvSt V) (hu : ∀ g c i, V.Ge 0 (X.u g c i))
    (x y : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (hy : y ∈ X.TySet V g) : x + y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨γ', lam', hγ', hlam', h1', h2'⟩ := hy
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  have hty : ∀ n, tyS V.l (fun s => (x + y) s n) = tyS V.l (fun s => x s n) + tyS V.l (fun s => y s n) :=
    fun n => tyS_add hl2 _ _
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (hu (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add, map_add, (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add, map_add]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hty, smul_add]
  · intro q
    have hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => (x + y) s (Sum.inl c)) else 0) =
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) +
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => y s (Sum.inl c)) else 0) := by
      intro c
      rw [hty]
      split_ifs
      · rw [smul_add]
      · rw [add_zero]
    simp only [hs]
    rw [Finset.sum_add_distrib, hty, h2 q, h2' q]
    abel

private theorem powerSeries_rescale_smul (a c : C) (f : PowerSeries C) :
    PowerSeries.rescale a (c • f) = c • PowerSeries.rescale a f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

private theorem alongCv_rescale_eq_rescale_alongCv {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (a : C) (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.rescale a (γ i)) f = PowerSeries.rescale a (alongCv γ f) := by
  simp only [PowerSeries.rescale_eq_subst]
  exact alongCv_repar hγ (by simp) f

private theorem tyS_neg_eq_rescale_neg_one_of_odd {l : ℕ} (hl : Odd l) (a : ℕ → C) :
    tyS l (fun s => -a s) = PowerSeries.rescale (-1) (tyS l a) := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h
  · rw [← h, (hl.pow).neg_one_pow]
    ring
  · ring

private theorem isCv_rescale_neg_one (V : VF C) {σ : Type} {γ : σ → PowerSeries C} (h : IsCv V γ) :
    IsCv V (fun i => PowerSeries.rescale (-1 : C) (γ i)) := by
  intro i
  show PowerSeries.constantCoeff (PowerSeries.rescale (-1 : C) (γ i)) = 0 ∧
    ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale (-1 : C) (γ i)))
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (h i).1
  · have h2 := (h i).2 n
    rw [PowerSeries.coeff_rescale]
    rcases neg_one_pow_eq_or C n with e | e
    · rw [e, one_mul]
      exact h2
    · rw [e, neg_one_mul]
      unfold VF.Ge at h2 ⊢
      rw [V.v.map_neg]
      exact h2

theorem neg_mem (V : VF C) (g : Fin 2) (hodd : V.l ≠ 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    -x ∈ X.TySet V g := by
  have hl : Odd V.l := V.l_prime.odd_of_ne_two hodd
  unfold RawChart.TySet at hx ⊢
  obtain ⟨γ, lam, hγ, hlam, hlg, hq⟩ := hx
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  rw [Set.mem_setOf_eq]
  refine ⟨fun i => PowerSeries.rescale (-1 : C) (γ i), fun q => PowerSeries.rescale (-1 : C) (lam q),
    isCv_rescale_neg_one V hγ, isCv_rescale_neg_one V hlam, ?_, ?_⟩
  · intro i
    simp only [Pi.neg_apply]
    rw [alongCv_rescale_eq_rescale_alongCv hγ0, hlg i, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, powerSeries_rescale_smul]
  · intro q
    simp only [Pi.neg_apply]
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, hq q, alongCv_rescale_eq_rescale_alongCv hγ0]
    simp only [tyS_neg_eq_rescale_neg_one_of_odd hl, map_add, map_sub, map_sum, apply_ite ⇑(PowerSeries.rescale (-1 : C)), map_zero,
      powerSeries_rescale_smul]

theorem sum_mem (V : VF C) (g : Fin 2) (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g) {ι : Type} (s : Finset ι)
    (f : ι → ℕ → I g ⊕ JJ I g → C) (hf : ∀ i ∈ s, f i ∈ X.TySet V g) : ∑ i ∈ s, f i ∈ X.TySet V g := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact h0
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieValCut
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

def expAll (x : Fin dd) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun i : Fin dd => ∑ w : WVO I, (p w.1).u w.2.1 w.2.2 i •
    (MvPowerSeries.X w : MvPowerSeries (WVO I) C)) (un1 (Y.ex x))

def pull1 (F : PS C 1 dd) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) F

def rowOf {n : ℕ} (b : Fin n) (F : MvPowerSeries (WVO I) C) : MvPowerSeries (Fin n × WVO I) C :=
  MvPowerSeries.subst (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) F

def pullN {n : ℕ} (F : PS C n dd) : MvPowerSeries (Fin n × WVO I) C :=
  MvPowerSeries.subst (fun q : Fin n × Fin dd => rowOf q.1 (expAll Y p q.2)) F

def toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) F

def LogCoordSt : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (Q : MvPolynomial (Fin n × WVO I) C), IsImgO (fun o => Y.raw (p o)) cp uv P Q →
    ∀ F : PS C n dd, MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) cp uv P F) = jetAt0 Q (pullN Y p F)

def UnitSt : Prop :=
  PairsSep Y p → ∃ U : PS C 1 dd, IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0 ∧
    pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      pull1 Y p U * ∏ o, toAllS o (mvExp (Y.raw (p o)).hRow)

def GermLiftSt (H : ∀ o, (Y.raw (p o)).Hyps V) : Prop :=
  PairsSep Y p → ∀ (o : Orb) (S : ∀ g, Sys (((Y.raw (p o)).rowData (H o)).G g))
    (t : ∀ g, I o g → MvPowerSeries (I o g) C), (∀ g, (S g).IsT (t g)) →
    ∀ F ∈ IntGerm V t, ∃ G : PS C 1 dd, IntS V G ∧ pull1 Y p G = toAllS o F

end Defs

def LeafSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (H : X.Hyps V) (n : ℕ) (Po : MvPolynomial (Fin n × WV I) C)
    (kind : Fin n → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt Po kind →
    ∀ gr : Fin n → MvPowerSeries (WV I) C,
      jetAt0 Po (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) = ValOf (X.rowData H).hL Po kind gr

def ValEqPFromCutsSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (d : ℕ) [NeZero d]
    (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ),
    LogCoordSt Y p → UnitSt Y p → GermLiftSt Y p H → LeafSt → ValEqPSt Y p H Ls n

end Formalism.L2.FormalSeriesBounds
end
end

