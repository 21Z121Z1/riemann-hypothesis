import Formalism.LocalToGlobal.Columns.Bundle0023
import Formalism.LocalToGlobal.Columns.AtTOwedS
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.HermitianForms.Bundle0002

-- bundled from Formalism.LocalToGlobal.Columns.TiedAtT
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

include hPr in
theorem att_T_mem_under (P : {P // P ∈ Pr.vT u}) : (Pr.T u : 𝓞 X.F) ∈ (underPl X.F P.1).asIdeal := by
  show (Pr.T u : 𝓞 X.F) ∈ P.1.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast]
  exact T_mem hPr u P

def tieEV : {P // P ∈ Pr.vT u} ≃ {v : HeightOneSpectrum (𝓞 X.F) // (Pr.T u : 𝓞 X.F) ∈ v.asIdeal} :=
  Equiv.ofBijective (fun P => ⟨underPl X.F P.1, att_T_mem_under hPr u P⟩) (by
    constructor
    · intro P Q h
      have h1 : underPl X.F P.1 = underPl X.F Q.1 := congrArg Subtype.val h
      have hP : IsOver (underPl X.F P.1) P.1 := rfl
      have hQ : IsOver (underPl X.F P.1) Q.1 := by rw [h1]; rfl
      exact Subtype.ext ((basePi_of_ok hX hPr u).over_unique hc P.2 hP Q.1 Q.2 hQ).symm
    · rintro ⟨v, hv⟩
      obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).2 hv
      exact ⟨⟨P, hP⟩, Subtype.ext (HeightOneSpectrum.ext hov.symm)⟩)

theorem tieEV_over (P : {P // P ∈ Pr.vT u}) : IsOver (tieEV hc hX hPr u P).1 P.1 := rfl

theorem tieEV_val (P : {P // P ∈ Pr.vT u}) : (tieEV hc hX hPr u P).1 = underPl X.F P.1 := rfl

end Gen

section Val

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))

include hval in

theorem att_val_pos (w : Pl.Pl) (x : 𝓞 K) : (0 : WithTop ℤ) < Pl.val w (x : K) ↔ x ∈ (pw w).asIdeal := by
  by_cases hx : x = 0
  · subst hx
    have h0 : Pl.val w (((0 : 𝓞 K) : 𝓞 K) : K) = ⊤ := by
      rw [show (((0 : 𝓞 K) : 𝓞 K) : K) = 0 from rfl]
      exact (Pl.val w).map_zero
    rw [h0]
    exact ⟨fun _ => zero_mem _, fun _ => WithTop.coe_lt_top (0 : ℤ)⟩
  · have hx' : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext h)
    have h0 : (pw w).valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hx'
    rw [hval w _ hx', ← (pw w).valuation_lt_one_iff_mem (K := K)]
    unfold Formalism.BasicNotions.vAdd
    rw [← WithTop.coe_zero, WithTop.coe_lt_coe, neg_pos, ← WithZero.log_one, WithZero.log_lt_log h0 one_ne_zero]

include hval in

theorem att_resChar_mem (w : Pl.Pl) : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ (pw w).asIdeal := by
  rw [← att_val_pos Pl pw hval]
  have h := Pl.val_resChar w
  have e : ((((Pl.resChar w : ℕ) : 𝓞 K) : 𝓞 K) : K) = ((Pl.resChar w : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [e, h, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  exact_mod_cast Pl.ramIdx_pos w

end Val

section Seen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

include hc in

theorem att_mem_conjP (P : Pl X.E) (x : 𝓞 X.F) :
    algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime₂ P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal := by
  rw [mem_conjP, rll_cO_algebraMap hc]

theorem att_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    x ∈ (tieEV hc hX hPr u P).1.asIdeal ↔ X.embO (tauOfR hX hPr u w P) (algebraMap (𝓞 X.F) (𝓞 X.E) x) ∈ w.asIdeal := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dif_pos hw]
    rfl
  rw [e, ← mem_pullW]
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.1.asIdeal ↔ _
  rcases tauOfC_spec hX hPr u w hw P with h | h
  · rw [show pullW (tauOfC w P.1) w = P.1 from h]
  · rw [show pullW (tauOfC w P.1) w = conjPrime₂ P.1 from h, att_mem_conjP hc]

include hX hPr in
open Classical in

theorem att_seenP (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (τ : X.Tau) :
    X.embO τ (if decide (seenC Pr u w) = true then Pr.piT u else X.conjO (Pr.piT u)) ∈ w.asIdeal := by
  by_cases h : seenC Pr u w
  · rw [if_pos (decide_eq_true h)]
    exact h τ
  · rw [if_neg (by simpa using h)]
    exact ((seenC_or_seenBarC hX hPr u w hw).resolve_left h) τ

end Seen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem att_star_eq (x : d.host.E) : star x = d.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj d.host x

set_option maxHeartbeats 1000000 in

def atTTied (hH : HostHyp d) (u : d.what₂.Word) : CF.AtTTied (D := d.colRec a) u where
  eV := tieEV d.sp.cm d.hX d.hPr u
  piU := d.piT u
  piU_K := hH.piT_K u
  piU_norm := by
    have h := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piT_norm u)
    rw [map_mul, map_natCast] at h
    rw [← att_star_eq]
    exact h
  piU_cong := by
    rw [Ideal.mem_span_singleton]
    have h := d.hPr.piT_cong u
    have e : d.Pr.cond = d.host.QS * d.host.q * d.host.d := hH.cond_eq
    rw [e] at h
    exact h
  res := fun v => Ideal.Quotient.mk v.1.asIdeal
  res_surj := fun v => Ideal.Quotient.mk_surjective
  res_pi := fun v => Ideal.Quotient.eq_zero_iff_mem.2 ((rls_vT_iff d.hX d.hPr u v.1).1 v.2)
  res_conj := fun v pb hpb h => by
    have h1 : pb = cO d.X.E (d.Pr.piT u) := by
      apply RingOfIntegers.ext
      rw [hpb, ← att_star_eq]
      rfl
    exact (basePi_of_ok d.hX d.hPr u).conj_notMem v.2 (h1 ▸ Ideal.Quotient.eq_zero_iff_mem.1 h)
  res_v := fun v x => (Ideal.Quotient.eq_zero_iff_mem (I := v.1.asIdeal)).symm
  tauOf := fun w hw v x => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    exact (att_tauOf d.sp.cm d.hX d.hPr u (d.plEq w) hT v x).trans (att_val_pos d.what₂.places d.plEq hH.val_eq w _).symm
  seenP := fun w hw τ => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    have key : ∀ b : Bool, b = (open Classical in decide (seenC d.Pr u (d.plEq w))) →
        (0 : WithTop ℤ) < d.what₂.places.val w (d.embE (d.host.sigmaOf (d.eTau τ : d.R.GG)
          (if b = true then (d.piT u : d.host.E) else d.host.conj (d.piT u : d.host.E)))) := by
      intro b hb
      by_cases hs : seenC d.Pr u (d.plEq w)
      · have hb' : b = true := by rw [hb]; exact @decide_eq_true _ (Classical.propDecidable _) hs
        rw [if_pos hb']
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.Pr.piT u))).2 (hs τ)
      · have hb' : ¬ b = true := by rw [hb]; simpa using hs
        rw [if_neg hb', ← att_star_eq]
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.X.conjO (d.Pr.piT u)))).2
          (((seenC_or_seenBarC d.hX d.hPr u (d.plEq w) hT).resolve_left hs) τ)
    exact key _ rfl

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlChi
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV
open Formalism.L2.Forms (kv)

section Chi

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok)

theorem glc_extChi {κ K : Type} [CommRing κ] [Field K] {m : ℕ} (χ : Fin m → κˣ →* Kˣ) {a : ℕ} (ha : a < m) : extChi χ a = χ ⟨a, ha⟩ :=
  dif_pos ha

include hPr in
theorem glc_charP (i : Fin 2) {w : Pl X.E} (hw : w ∈ Pr.vG i) : CharP (kP w) (Pr.g i) := by
  have : Nontrivial (kP w) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  rw [CharP.charP_iff_prime_eq_zero (hPr.g_prime i)]
  have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 X.E) ∈ w.asIdeal := Ideal.absNorm_mem _
  rw [hPr.vG_norm i w hw] at h1
  have := Ideal.Quotient.eq_zero_iff_mem.2 h1
  rwa [map_natCast] at this

theorem glc_order {g : ℕ} [Fact g.Prime] {K : Type} [Field K] (σ₀ : K →+* ℂ) (om₀ : (ZMod g)ˣ →* Kˣ) (hinj : Function.Injective om₀) :
    orderOf (MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀) : MulChar (ZMod g) ℂ) = g - 1 := by
  set om : MulChar (ZMod g) ℂ := MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀) with hom
  have hpow : ∀ k : ℕ, om ^ k = 1 ↔ ∀ x : (ZMod g)ˣ, x ^ k = 1 := by
    intro k
    constructor
    · intro h x
      have h1 := DFunLike.congr_fun h (x : ZMod g)
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hom, MulChar.ofUnitHom_coe] at h1
      have h2 : σ₀ ((om₀ (x ^ k) : Kˣ) : K) = σ₀ 1 := by
        rw [map_pow, Units.val_pow_eq_pow_val, map_pow, map_one]
        exact h1
      have h3 : om₀ (x ^ k) = om₀ 1 := by
        rw [map_one]
        exact Units.ext (σ₀.injective h2)
      exact hinj h3
    · intro h
      ext x
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hom, MulChar.ofUnitHom_coe, ← Units.val_pow_eq_pow_val, ← map_pow, h x, map_one,
        Units.val_one]
  have hcard : Monoid.exponent (ZMod g)ˣ = g - 1 := by
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units]
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, hpow]
    intro x
    rw [← hcard]
    exact Monoid.pow_exponent_eq_one x
  · rw [← hcard]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one ((hpow _).1 (pow_orderOf_eq_one om))

theorem glc_pow (i : Fin 2) : ∃ om : MulChar (ZMod (Pr.g i)) ℂ, orderOf om = Pr.g i - 1 ∧
    ∀ v h a (n : ℤ), a < m → (tieGLoc hPr S Ch σ₀ hCh).chiB i v h a (n : kv X.F v) = (om ^ (2 * (a + 1))) (n : ZMod (Pr.g i)) := by
  haveI : Fact (Pr.g i).Prime := ⟨hPr.g_prime i⟩
  obtain ⟨om₀, hinj, hom⟩ := hCh.chi_om i
  refine ⟨MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp om₀), glc_order σ₀ om₀ hinj, ?_⟩
  intro v h a n ha
  haveI := glc_charP hPr i (gwOf_mem hc hPr i v h)
  have hcast : (n : kv X.F v) = S.eK hPr i v h (n : kP (gwOf hc hPr i v h).1) := (map_intCast _ n).symm
  show glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) a) (n : kv X.F v) = _
  by_cases hn : ((Pr.g i : ℕ) : ℤ) ∣ n
  · have h1 : (n : ZMod (Pr.g i)) = 0 := (CharP.intCast_eq_zero_iff _ (Pr.g i) n).2 hn
    have h2 : (n : kP (gwOf hc hPr i v h).1) = 0 := (CharP.intCast_eq_zero_iff _ (Pr.g i) n).2 hn
    rw [hcast, h1, h2, map_zero, MulChar.map_zero, MulChar.map_zero]
  · have h1 : (n : ZMod (Pr.g i)) ≠ 0 := fun h0 => hn ((CharP.intCast_eq_zero_iff _ (Pr.g i) n).1 h0)
    have h2 : (n : kP (gwOf hc hPr i v h).1) ≠ 0 := fun h0 => hn ((CharP.intCast_eq_zero_iff _ (Pr.g i) n).1 h0)
    have h3 : (n : kv X.F v) ≠ 0 := by
      rw [hcast]
      exact fun h0 => h2 ((map_eq_zero_iff _ (S.eK hPr i v h).injective).1 h0)
    let a' : (ZMod (Pr.g i))ˣ := Units.mk0 _ h1
    let x : (kP (gwOf hc hPr i v h).1)ˣ := Units.map (S.eK hPr i v h).symm.toRingHom.toMonoidHom (Units.mk0 _ h3)
    have hx : (x : kP (gwOf hc hPr i v h).1) = (n : kP (gwOf hc hPr i v h).1) := by
      show (S.eK hPr i v h).symm (n : kv X.F v) = _
      rw [hcast, RingEquiv.symm_apply_apply]
    have hval : (x : kP (gwOf hc hPr i v h).1) = (((a' : ZMod (Pr.g i)).val : ℕ) : kP (gwOf hc hPr i v h).1) := by
      rw [hx, ZMod.natCast_val]
      exact (map_intCast (ZMod.castHom (dvd_refl (Pr.g i)) (kP (gwOf hc hPr i v h).1)) n).symm
    have h4 := hom (gwOf hc hPr i v h) (gwOf_mem hc hPr i v h) ⟨a, ha⟩ a' x hval
    rw [hcast, ← hx, glmChi_apply, glc_extChi _ ha, h4]
    have h5 : (n : ZMod (Pr.g i)) = (a' : ZMod (Pr.g i)) := rfl
    rw [h5, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, Units.val_pow_eq_pow_val, map_pow]
    rfl

theorem tieGLoc_chiTied : Formalism.L2.Forms.CharacterCompatible (tieGLoc hPr S Ch σ₀ hCh) m where
  dist i v h a b ha hb e := by
    have h1 : Ch.chi ⟨a, ha⟩ (gwOf hc hPr i v h) = Ch.chi ⟨b, hb⟩ (gwOf hc hPr i v h) := by
      ext x
      have h2 := DFunLike.congr_fun e (S.eK hPr i v h (x : kP (gwOf hc hPr i v h).1))
      change glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) a) _ =
        glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) b) _ at h2
      rw [glmChi_apply, glmChi_apply, glc_extChi _ ha, glc_extChi _ hb] at h2
      exact σ₀.injective h2
    have h3 := hCh.chi_inj (gwOf hc hPr i v h) h1
    exact congrArg Fin.val h3
  same i v h v' h' a n ha := by
    obtain ⟨om, -, hom⟩ := glc_pow hPr S Ch σ₀ hCh i
    rw [hom v h a n ha, hom v' h' a n ha]
  pow i := glc_pow hPr S Ch σ₀ hCh i

end Chi

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlev
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV
open Formalism.L2.Forms (kv redM InJ)

section Red

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E))
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
  (halg : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a))
  (w : Pl E) (hw : ∀ a ∈ w.asIdeal, gloRho v spl halg (oToS F E a) = 0)

theorem gco_exists_red (hT : v ∉ plUnder F ST) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) :
    ∃ M : GL (Fin n) (kP w), (M : Matrix (Fin n) (Fin n) (kP w)).map (gloE v spl halg w hw) =
      redM F v ((bc (gloPhi v spl) x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hx.2
  have hS := rll_put_mem_St n v hxS
  refine ⟨redAt 1 w ⟨rll_put n v x, hS⟩, ?_⟩
  rw [gco_red_map n v spl halg w hw hS, rll_put_self]

end Red

section Diag

variable {F : Type} [Field F] [NumberField F] (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 F))

open Classical in

def glvU (c : (v.adicCompletionIntegers F)ˣ) (b : Fin n) : (v.adicCompletionIntegers F)ˣ := if b = lastIdx n then c else 1

def glvD (c : (v.adicCompletionIntegers F)ˣ) : GL (Fin n) (v.adicCompletion F) where
  val := Matrix.diagonal fun b => ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F)
  inv := Matrix.diagonal fun b => (((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact congrArg Subtype.val (glvU n v c b).mul_inv
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact congrArg Subtype.val (glvU n v c b).inv_mul

theorem glvD_one : glvD n v 1 = 1 := by
  apply Units.ext
  show Matrix.diagonal _ = 1
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  unfold glvU
  split_ifs <;> rfl

theorem glvU_res {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1) (b : Fin n) :
    IsLocalRing.residue (v.adicCompletionIntegers F) (glvU n v c b) = 1 := by
  unfold glvU
  split_ifs
  · exact hc1
  · rw [Units.val_one, map_one]

theorem glvU_res_inv {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1) (b : Fin n) :
    IsLocalRing.residue (v.adicCompletionIntegers F) ((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) = 1 := by
  have h := congrArg (IsLocalRing.residue (v.adicCompletionIntegers F)) (glvU n v c b).inv_mul
  rwa [map_mul, glvU_res n v hc1, mul_one, map_one] at h

theorem glv_red_conj {c : (v.adicCompletionIntegers F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers F) c = 1)
    (A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hA : ∀ a b, A a b ∈ v.adicCompletionIntegers F) :
    redM F v ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = redM F v A := by
  ext a b
  have e : ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) a b =
      (((((glvU n v c a)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * ⟨A a b, hA a b⟩ * (glvU n v c b :
        v.adicCompletionIntegers F) : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    show ((Matrix.diagonal (fun b => ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
      v.adicCompletion F)) * A : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      Matrix.diagonal (fun b => ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F))) a b = _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  have hm : ((((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * A *
      (glvD n v c : Matrix (Fin n) (Fin n) (v.adicCompletion F))) a b ∈ v.adicCompletionIntegers F := by
    rw [e]; exact Subtype.mem _
  unfold redM
  rw [dif_pos (hA a b), dif_pos hm]
  have e2 : (⟨_, hm⟩ : v.adicCompletionIntegers F) =
      (((glvU n v c a)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) * ⟨A a b, hA a b⟩ * (glvU n v c b :
        v.adicCompletionIntegers F) := Subtype.ext e
  rw [e2, map_mul, map_mul, glvU_res n v hc1, glvU_res_inv n v hc1, one_mul, mul_one]

theorem glv_mulVec_int (c : (v.adicCompletionIntegers F)ˣ) (x : Fin n → v.adicCompletion F) :
    (∀ b, (((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
      v.adicCompletionIntegers F) ↔ ∀ b, x b ∈ v.adicCompletionIntegers F := by
  refine forall_congr' fun b => ?_
  have e : (((glvD n v c)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b =
      ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) * x b := by
    show (Matrix.diagonal (fun b => ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
      v.adicCompletion F))).mulVec x b = _
    rw [Matrix.mulVec_diagonal]
  rw [e]
  constructor
  · intro h
    have h2 := mul_mem (glvU n v c b : v.adicCompletionIntegers F).2 h
    rw [← mul_assoc] at h2
    have h3 : ((glvU n v c b : v.adicCompletionIntegers F) : v.adicCompletion F) *
        ((((glvU n v c b)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 :=
      congrArg Subtype.val (glvU n v c b).mul_inv
    rwa [h3, one_mul] at h2
  · intro h
    exact mul_mem (Subtype.mem _) h

end Diag

section Lev

variable {X : Fields} {Pr : Primes X} {hc : Formalism.BasicNotions.CMData X.F X.E} (hPr : Pr.Ok) (S : GSplit (Pr := Pr) hc) {m : ℕ}
  (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (hCh : Ch.Ok)
  {n : ℕ} [NeZero n] {ST : Finset (Pl X.E)} {π : 𝓞 X.E} {T f : ℕ} (Λ : LevFam X.E X.K n Pr.vGs)

theorem glv_chr (h : ↥Λ.grp) : Λ.chr h = ∏ w : Pr.vGs, (Λ w).lam ⟨h.1 w, h.2 w (Set.mem_univ w)⟩ := by
  have h1 : Λ.chr h = (∏ i : Pr.vGs, ((Λ i).lam).comp (piProj (fun w => (Λ w).H) i))
      (show ↥(Subgroup.pi Set.univ fun w : Pr.vGs => (Λ w).H) from h) := rfl
  rw [h1, MonoidHom.finsetProd_apply]
  rfl

theorem glv_mat_red (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal)
    {c : (v.adicCompletionIntegers X.F)ˣ} (hc1 : IsLocalRing.residue (v.adicCompletionIntegers X.F) c = 1)
    (x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F))
    (hx : ∀ a b, (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) a b ∈ Formalism.BasicNotions.intV X.E v) :
    redM X.F v ((tieGLoc hPr S Ch σ₀ hCh).mat i v h (glvD n v c) x) =
      redM X.F v ((bc (gloPhi v (S.sp i v h)) x : GL (Fin n) (v.adicCompletion X.F)) : Matrix (Fin n) (Fin n) (v.adicCompletion X.F)) :=
  glv_red_conj n v hc1 _ fun a b => gloPhi_int v (S.sp i v h) (S.sp_alg i v h) _ (hx a b)

def glevOf (hB : BasePi ST π) (hTπ : π * cO X.E π = (T : 𝓞 X.E)) (hST : ∀ P : Pl X.E, P ∈ ST ↔ π ∈ P.asIdeal)
    (hcard : ∀ P ∈ ST, Nat.card (𝓞 X.E ⧸ P.asIdeal) = T)
    (hSG : ∀ v : HeightOneSpectrum (𝓞 X.F), (T : 𝓞 X.F) ∈ v.asIdeal → v ∉ plUnder X.F Pr.vGs)
    (hidx : (baseLb X.E n ST).toAddSubgroup.relIndex
      (Submodule.span (𝓞 X.E) (Formalism.BasicNotions.dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n ST))).toAddSubgroup =
        T ^ (2 * f))
    (a t nb skip fc : ℕ) (zl : Bool)
    (c : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal → (v.adicCompletionIntegers X.F)ˣ)
    (hc1 : ∀ i v h, IsLocalRing.residue (v.adicCompletionIntegers X.F) (c i v h) = 1)
    (hmem : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)), M ∈ (Λ (gwOf hc hPr i v h)).H ↔
      InJ a t fc zl ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h)))
    (hlam : ∀ i v h (M : GL (Fin n) (kP (gwOf hc hPr i v h).1)) (hM : M ∈ (Λ (gwOf hc hPr i v h)).H),
      σ₀ (((Λ (gwOf hc hPr i v h)).lam ⟨M, hM⟩ : X.Kˣ) : X.K) =
        Formalism.L2.Forms.lamJ (glmPsi (S.eK hPr i v h) σ₀ (Ch.psi0 (gwOf hc hPr i v h)))
          (fun s => glmChi (S.eK hPr i v h) σ₀ (extChi (fun s => Ch.chi s (gwOf hc hPr i v h)) s)) a t nb skip
          ((M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h))) :
    Formalism.L2.Forms.GLev (stepOf hc n (fun w => (Λ w).H) hB hTπ hST hcard hSG hidx ((Units.map σ₀.toMonoidHom).comp Λ.chr))
      (tieGLoc hPr S Ch σ₀ hCh) a t nb skip fc zl where
  fr i v h := glvD n v (c i v h)
  fr_lat i v h x := by
    rw [glv_mulVec_int]
    refine (gco_fr_lat n ST v (S.sp i v h) (S.sp_alg i v h)
      (fun hT => hSG v ((mem_plUnder_iff_norm hc hST T hTπ v).1 hT) ⟨_, (gwOf hc hPr i v h).2, gwOf_over hc hPr i v h⟩) x).trans ?_
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  mem i v h x hx := by
    have hT : v ∉ plUnder X.F ST := fun hT =>
      hSG v ((mem_plUnder_iff_norm hc hST T hTπ v).1 hT) ⟨_, (gwOf hc hPr i v h).2, gwOf_over hc hPr i v h⟩
    have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat X.E n)) := by
      rw [← rll_locL_base n ST v hT]; exact hx.2
    rw [rll_locL_std] at hxS
    rw [glv_mat_red hPr S Ch σ₀ hCh i v h (hc1 i v h) x ((afsplit_stab_iff _ x).1 hxS).1]
    refine (gco_mem_levLoc hc n ST Pr.vGs v (S.sp i v h) (S.sp_alg i v h) (fun w => (Λ w).H) (gwOf hc hPr i v h) (S.ker hPr i v h)
      (gwOf_over hc hPr i v h) (fun w' hw' => gwOf_uniq hc hPr i v h w' hw') hT x hx).trans ?_
    constructor
    · rintro ⟨M, hM, e⟩
      rw [← e]
      exact (hmem i v h M).1 hM
    · intro hJ
      obtain ⟨M, e⟩ := gco_exists_red hc n ST v (S.sp i v h) (S.sp_alg i v h) _ (S.ker hPr i v h) hT x hx
      refine ⟨M, (hmem i v h M).2 ?_, e⟩
      have e' : (M : Matrix (Fin n) (Fin n) (kP (gwOf hc hPr i v h).1)).map (S.eK hPr i v h) = _ := e
      rw [e']
      exact hJ
  chi_eq x := by
    have hJ0 : (x : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) ∈ J0 hc n ST := unipotentLevel_le_mirabolicLevel hc n ST Pr.vGs _ x.2
    have hred : ∀ w : Pr.vGs, redAt 1 w.1 ⟨x.1, congruence_subgroup_le_stabilizer hc n ST hJ0⟩ ∈ (Λ w).H := fun w =>
      ((mem_levU hc n ST Pr.vGs _).1 x.2).2 w (Set.mem_univ w)
    have h1 : ((levTyp ((Units.map σ₀.toMonoidHom).comp Λ.chr) x : ℂˣ) : ℂ) =
        ∏ w : Pr.vGs, (σ₀ (((Λ w).lam ⟨redAt 1 w.1 ⟨x.1, congruence_subgroup_le_stabilizer hc n ST hJ0⟩, hred w⟩ : X.Kˣ) : X.K))⁻¹ := by
      show ((((Units.map σ₀.toMonoidHom).comp Λ.chr) (levRed hc n ST Pr.vGs _ x))⁻¹ : ℂˣ).1 = _
      rw [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]
      congr 1
      show σ₀ ((Λ.chr (levRed hc n ST Pr.vGs _ x) : X.Kˣ) : X.K) = _
      rw [glv_chr, Units.coe_prod, map_prod]
      rfl
    refine h1.trans ?_
    rw [glk_prod hc hPr]
    refine Finset.prod_congr rfl fun i _ => finprod_congr fun v => finprod_congr fun h => ?_
    rw [hlam i v h, glv_mat_red hPr S Ch σ₀ hCh i v h (hc1 i v h) _ (fun a b =>
      afsplit_prV_int v _ (((rll_mem_St_iff n x.1).1 (congruence_subgroup_le_stabilizer hc n ST hJ0)).1 a b))]
    congr 2
    exact gco_red_map n v (S.sp i v h) (S.sp_alg i v h) _ (S.ker hPr i v h) (congruence_subgroup_le_stabilizer hc n ST hJ0)
  chi_unit x := gco_chi_unit hc n ST Pr.vGs _ _ x

end Lev

end Formalism.L2.Col
end
end

