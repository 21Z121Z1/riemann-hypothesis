import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0069
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabellingInertFrobeniusNotConj
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertLabelling

open GlobalTheory.LevelsOrbits

lemma ordP_dvd_of_pos_eq (N : NumDatum) (l : ℕ) (z : RPl N.R) (u : ℕ) (h : N.pos l z u = z) : N.ordP l ∣ u := by
  unfold NumDatum.pos at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only at h1 h2
  have h3 : u • N.hP l = 0 := by simpa using h2
  unfold NumDatum.ordP
  by_cases hc : N.cls l = PrimeClass.signal
  · rw [if_pos hc]
    have ho : ¬ Odd u := by
      intro ho
      rw [decide_eq_true (⟨hc, ho⟩ : N.cls l = PrimeClass.signal ∧ Odd u)] at h1
      cases hz : z.1 <;> simp [hz] at h1
    obtain ⟨t, rfl⟩ := Nat.not_odd_iff_even.1 ho
    rw [← two_mul]
    refine Nat.mul_dvd_mul_left 2 (addOrderOf_dvd_of_nsmul_eq_zero ?_)
    rw [← mul_smul, mul_two, h3]
  · rw [if_neg hc]
    exact addOrderOf_dvd_of_nsmul_eq_zero h3

lemma pos_inj (N : NumDatum) (l : ℕ) (z : RPl N.R) (s t : ZMod (N.ordP l))
    (h : N.pos l z s.val = N.pos l z t.val) : s = t := by
  wlog hst : s.val ≤ t.val generalizing s t
  · exact (this t s h.symm (not_le.1 hst).le).symm
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hst
  rw [hu, ← pos_add] at h
  have hd := ordP_dvd_of_pos_eq N l _ u h.symm
  have hlt := ZMod.val_lt t
  have : u = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  apply ZMod.val_injective
  omega

def orbSetoid (N : NumDatum) (l : ℕ) : Setoid (RPl N.R) where
  r z z' := ∃ s : ℕ, N.pos l z s = z'
  iseqv := ⟨fun z => ⟨N.ordP l * 0, pos_mul_period N l z 0⟩, fun {z z'} ⟨s, hs⟩ => ⟨(N.ordP l - 1) * s, by
      have hp : 0 < N.ordP l := Nat.pos_of_ne_zero (NeZero.ne _)
      obtain ⟨n, hn⟩ : ∃ n, N.ordP l = n + 1 := ⟨N.ordP l - 1, by omega⟩
      rw [← hs, pos_add, show s + (N.ordP l - 1) * s = N.ordP l * s by rw [hn, Nat.add_sub_cancel]; ring,
        pos_mul_period]⟩,
    fun {a b c} ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s + t, by rw [← pos_add, hs, ht]⟩⟩

lemma exists_reps (N : NumDatum) (l : ℕ) : ∃ Z : Finset (RPl N.R),
    ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP l), p.1 ∈ Z ∧ N.pos l p.1 p.2.val = z' := by
  refine ⟨Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z, fun z' => ?_⟩
  obtain ⟨s, hs⟩ : (orbSetoid N l).r (Quotient.mk (orbSetoid N l) z').out z' := Quotient.mk_out z'
  have key : ∀ p : RPl N.R × ZMod (N.ordP l),
      p.1 ∈ (Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z) ∧ N.pos l p.1 p.2.val = z' →
      p.1 = (Quotient.mk (orbSetoid N l) z').out := by
    rintro p ⟨h1, h2⟩
    rw [← (Finset.mem_filter.1 h1).2]
    congr 1
    exact Quotient.sound ⟨_, h2⟩
  refine ⟨((Quotient.mk (orbSetoid N l) z').out, (s : ZMod (N.ordP l))), ⟨?_, ?_⟩, fun p hp => ?_⟩
  · simp
  · rw [ZMod.val_natCast, pos_mod, hs]
  · have h1 := key p hp
    refine Prod.ext h1 (pos_inj N l p.1 _ _ ?_)
    rw [hp.2, ZMod.val_natCast, pos_mod, h1, hs]

lemma even_ordP (N : NumDatum) (l : ℕ) (hI : Inert N l) (hC : ¬ ConjIn N l) : Even (N.ordP l) :=
  GlobalTheory.GoodDepth.even_ordP_of_not_conjIn hI hC

lemma bg_succ {d : ℕ} [NeZero d] (hd : Even d) (s : ZMod d) (g : Fin 2) : g = RF.bg (s + 1) ↔ ¬ g = RF.bg s := by
  have h : Even (s + 1).val ↔ ¬ Even s.val := by
    have e : s + 1 = ((s.val + 1 : ℕ) : ZMod d) := by simp
    rw [e, ZMod.val_natCast, ← Nat.even_add_one, Nat.even_iff, Nat.even_iff,
      Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hd)]
  unfold RF.bg
  by_cases hs : Even s.val
  · rw [if_pos hs, if_neg (fun hh => h.1 hh hs)]; fin_cases g <;> simp
  · rw [if_neg hs, if_pos (h.2 hs)]; fin_cases g <;> simp

lemma pos_succ (N : NumDatum) (l : ℕ) (z : RPl N.R) (s : ZMod (N.ordP l)) :
    N.pos l z (s + 1).val = N.pos l (N.pos l z s.val) 1 := by
  have e : s + 1 = ((s.val + 1 : ℕ) : ZMod (N.ordP l)) := by simp
  rw [e, ZMod.val_natCast, pos_mod, pos_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

lemma inPsi_conj_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have h0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by linear_combination this)
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [← map_pow, this, map_neg, map_natCast]
  have h2 : ∀ w : ℂ, w ^ 2 = -(H.d : ℂ) → starRingEnd ℂ w = -w := by
    intro w hw
    have hre := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp [pow_two] at hre him
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have : w.re = 0 := by
      by_contra hne
      have : w.im = 0 := by
        have : w.re * w.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg w.re]
    apply Complex.ext <;> simp [this]
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq, h2 _ h1]
  have h3 : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm)
  constructor
  · intro a b
    exact h0 (by linear_combination (-1/2 : ℂ) * a - (1/2 : ℂ) * b)
  · intro a
    rw [h3.resolve_left a, neg_neg]

lemma embK_conj_bar {lv : Level H} (c : Coeff lv) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c (ComplexEmbedding.conjugate τ) x := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

lemma conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
  ComplexEmbedding.involutive_conjugate E τ

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → Inert N V.l → ¬ ConjIn N V.l → ∀ j : ℕ, ∃ Z : Finset (RPl N.R), RF.IsReps (parOf N j V.l) Z ∧ Z.Nonempty ∧ Even (N.ordP V.l) ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod (N.ordP V.l) => tauIn N pl V.l x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauIn N pl V.l z g) ∧ ∀ s, tauIn N pl V.l z 1 s = ComplexEmbedding.conjugate (tauIn N pl V.l z 0 s) := by
  intro E _ _ _ H lv c N pl hT la T io C _ _ V ι _ hl hla hI hC j
  obtain ⟨Z, hZ⟩ := exists_reps N V.l
  have hev := even_ordP N V.l hI hC
  have hin : ∀ z, InPsi H (pl z) := fun z => (hT.psi _).2 ⟨z, rfl⟩
  have hne : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z') := fun z z' h =>
    (inPsi_conj_iff (pl z')).1 (h ▸ hin z) (hin z')
  have hcinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    (ComplexEmbedding.involutive_conjugate E).injective
  refine ⟨Z, hZ, ?_, hev, ⟨?_, ?_⟩, fun z g => ⟨fun s x => ?_, fun s => ?_⟩⟩
  · obtain ⟨p, hp, -⟩ := hZ (false, 0)
    exact ⟨p.1, hp.1⟩
  · rintro ⟨z, g, s⟩ ⟨z', g', s'⟩ h
    have main : N.pos V.l z.1 s.val = N.pos V.l z'.1 s'.val → (g = RF.bg s ↔ g' = RF.bg s') →
        (z, g, s) = (z', g', s') := by
      intro h1 h2
      have := (hZ _).unique (y₁ := (z.1, s)) (y₂ := (z'.1, s')) ⟨z.2, h1⟩ ⟨z'.2, rfl⟩
      obtain ⟨a, b⟩ := Prod.mk.inj this
      obtain rfl := Subtype.ext a
      subst b
      have : g = g' := (by decide : ∀ g g' b : Fin 2, (g = b ↔ g' = b) → g = g') _ _ _ h2
      rw [this]
    dsimp only [tauIn] at h
    by_cases a : g = RF.bg s <;> by_cases b : g' = RF.bg s'
    · rw [if_pos a, if_pos b] at h
      exact main (hT.inj h) (by tauto)
    · rw [if_pos a, if_neg b] at h
      exact absurd h (hne _ _)
    · rw [if_neg a, if_pos b] at h
      exact absurd h.symm (hne _ _)
    · rw [if_neg a, if_neg b] at h
      exact main (hT.inj (hcinj h)) (by tauto)
  · intro τ
    by_cases h : InPsi H τ
    · obtain ⟨z', rfl⟩ := (hT.psi _).1 h
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, RF.bg p.2, p.2), ?_⟩
      dsimp only [tauIn]
      rw [if_pos rfl, hp.2]
    · obtain ⟨z', hz'⟩ := (hT.psi _).1 ((inPsi_conj_iff τ).2 h)
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, RF.bg (p.2 + 1), p.2), ?_⟩
      dsimp only [tauIn]
      rw [if_neg ((bg_succ hev _ _).1 rfl), hp.2, hz', conj_conj]
  · have hf : ∀ (w : RPl N.R) (x : 𝓞 E), V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl (N.pos V.l w 1))) x -
        emA3 io ι (pl w) x ^ V.l) := by
      intro w x
      obtain ⟨y, hy, e⟩ := hT.frob la (hl ▸ hI) w x
      have := hla y hy
      rw [e, ← hl, map_sub, map_sub, map_pow, map_pow] at this
      exact this
    unfold tauIn
    rw [pos_succ]
    by_cases a : g = RF.bg s
    · rw [if_pos a, if_neg (fun hh => (bg_succ hev _ _).1 hh a)]
      exact hf _ _
    · rw [if_neg a, if_pos ((bg_succ hev _ _).2 a)]
      have := hf (N.pos V.l z s.val) (H.bar x)
      simp only [emA3, RingHom.comp_apply, embK_conj_bar, conj_conj] at this ⊢
      exact this
  · unfold tauIn
    by_cases a : (0 : Fin 2) = RF.bg s
    · rw [if_pos a, if_neg (by rw [← a]; decide)]
    · rw [if_neg a, if_pos (by revert a; generalize RF.bg s = b; revert b; decide), conj_conj]

end GlobalTheory.InertLabelling
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SeparatedEmbeddingsDirectionsTypedBasis
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeparatedDirections

theorem directions_typed_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (A : Type) [Fintype A] (tau : A → (E →+* ℂ)), (∀ s s', s ≠ s' → ∃ x : 𝓞 E, V.v (emA3 io ι (tau s) x - emA3 io ι (tau s') x) = 0) → (∀ s (x : Fin (Dw.mult (tau s))) i, V.Ge 0 (ι (chartUnitVectors C3 ⟨tau s, x⟩ i))) ∧ (∀ s (x : Fin (Dw.mult (tau s))) (a : 𝓞 E), linAct (Y.B.A.act a) (fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) = emA3 io ι (tau s) a • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i)) ∧ (∃ w : Fin (chD C3.ch) → (Σ s : A, Fin (Dw.mult (tau s))) → C, (∀ i q, V.Ge 0 (w i q)) ∧ ∀ q q' : (Σ s : A, Fin (Dw.mult (tau s))), ∑ i, ι (chartUnitVectors C3 ⟨tau q.1, q.2⟩ i) * w i q' = if q = q' then 1 else 0) ∧ ∀ s (v : Fin (chD C3.ch) → C), (∀ a : 𝓞 E, linAct (Y.B.A.act a) v = emA3 io ι (tau s) a • v) → ∃ b : Fin (Dw.mult (tau s)) → C, v = ∑ x, b x • fun i => ι (chartUnitVectors C3 ⟨tau s, x⟩ i) := by
  intro E _ _ _ H Dw l Xo c _ hs T io y C3 C _ _ V ι hι k Y hY A _ tau hsep
  letI := io.toAlgebra
  have hval : ∀ x : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr x)) :=
    (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1
  have huv : ∀ ℓ i, chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) := fun ℓ i =>
    C3.gen.1.2.2.2.2.2.2 ℓ i
  have hint : ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    GlobalTheory.LabelledDirections.ge_zero_of_isIntegral V
      (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  let M : 𝓞 E → Matrix (Fin (chD C3.ch)) (Fin (chD C3.ch)) C := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act a i)
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (M a).mulVec (fun s => ι (chartUnitVectors C3 ℓ s)) =
      emA3 io ι ℓ.1 a • fun s => ι (chartUnitVectors C3 ℓ s) := by
    intro a ℓ
    funext i
    have h := congrArg ι (GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 C3.ch a ℓ i)
    rw [map_sum, map_mul] at h
    refine Eq.trans ?_ h
    show ∑ j, M a i j * ι (chartUnitVectors C3 ℓ j) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    simp only [M, hY.act, MvPowerSeries.coeff_map]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s x i
    rw [huv]
    exact hval _
  · intro s x a
    exact heig a ⟨tau s, x⟩
  · have key := GlobalTheory.SatBlocks.saturated_blocks_summand C V.v (𝓞 E) A
      (fun a => Dw.mult (tau a)) (chD C3.ch) M (fun a x => emA3 io ι (tau a) x)
      (fun q i => ι (chartUnitVectors C3 ⟨tau q.1, q.2⟩ i)) (fun x i j => Y.intAct x i _) (fun a x => hint _ x)
      (fun x q => heig x ⟨tau q.1, q.2⟩)
      hsep
      (fun a => by
        obtain ⟨⟨w, emb, hw1, hw2⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C3 (tau a)
        obtain ⟨W, hW⟩ := GlobalTheory.LabelledDirections.exists_dual w emb hw2
        refine ⟨fun s i => ι (algebraMap T.V T.Fr (W s i)), fun s i => hval _, fun i i' => ?_⟩
        have := congrArg (ι.comp (algebraMap T.V T.Fr)) (hW i i')
        rw [map_sum, apply_ite (ι.comp (algebraMap T.V T.Fr)), map_one, map_zero] at this
        refine Eq.trans ?_ this
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_mul, hw1]
        dsimp only
        rw [huv]
        rfl)
    obtain ⟨w, h1, h2⟩ := key
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  · intro a v hv
    have hinj : Function.Injective fun (τ : E →+* ℂ) (x : 𝓞 E) => emA3 io ι τ x := by
      intro τ τ' h
      by_contra hne
      obtain ⟨b, hb⟩ := GlobalTheory.EigDir.embK_sep c τ τ' hne
      exact hb ((ι.comp io).injective (congrFun h b))
    exact GlobalTheory.eigenvector_mem_span_block_of_basis T.Fr C ι (𝓞 E) (E →+* ℂ) Dw.mult (chD C3.ch) M
      (fun τ x => emA3 io ι τ x) (chartUnitVectors C3) hinj heig C3.ch.chart.basis (tau a) v hv

end GlobalTheory.SeparatedDirections
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.SmallTors

variable {q : ℕ} [hq : Fact q.Prime]

lemma norm_zc' (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap']
  rfl

lemma norm_nat_coprime {m : ℕ} (hm : Nat.Coprime m q) : ‖(m : ℂ_[q])‖ = 1 := by
  have h0 : (m : ℂ_[q]) = zc (m : ℤ_[q]) := by simp [zc]
  rw [h0, norm_zc']
  have h1 : ¬ ‖((m : ℤ) : ℤ_[q])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    have := (Nat.Prime.coprime_iff_not_dvd hq.out).1 hm.symm
    exact_mod_cast this
  push_cast at h1
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h1)

lemma norm_q_pow (n : ℕ) : ‖((q : ℂ_[q])) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have h0 : (q : ℂ_[q]) ^ n = zc ((q : ℤ_[q]) ^ n) := by simp [zc]
  rw [h0, norm_zc', PadicInt.norm_p_pow]

lemma norm_eq_one {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) : ‖ξ‖ = 1 := by
  have : ξ = (ξ - 1) + 1 := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne), norm_one]
  exact max_eq_right h.le

lemma norm_pow_sub_one {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) (n : ℕ) : ‖ξ ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ξ ^ (n + 1) - 1 = ξ * (ξ ^ n - 1) + (ξ - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
    rw [norm_mul, norm_eq_one h, one_mul]; exact ih

lemma norm_geom_sub {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, ξ ^ i - n‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ∑ i ∈ Finset.range (n + 1), ξ ^ i - ((n + 1 : ℕ) : ℂ_[q])
        = (∑ i ∈ Finset.range n, ξ ^ i - n) + (ξ ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (norm_pow_sub_one h n))

lemma eq_one_of_pow {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) {m : ℕ} (hm : Nat.Coprime m q) (h1 : ξ ^ m = 1) :
    ξ = 1 := by
  have h2 := geom_sum_mul ξ m
  rw [h1, sub_self, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · have h3 := norm_geom_sub h m
    rw [h2, zero_sub, norm_neg, norm_nat_coprime hm] at h3
    exact absurd h3 (lt_irrefl _)
  · exact sub_eq_zero.1 h2

lemma inOK_int (d : ℕ) (k : ℤ) : InOK d (k : ℂ) := ⟨k, 0, by simp⟩

lemma inOK_of_eq {d : ℕ} {x y : ℂ} (h : InOK d x) (e : x = y) : InOK d y := e ▸ h

end GlobalTheory.MomOne.SmallTors

namespace GlobalTheory.MomOne
open SmallTors

theorem smallTors : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → (∀ p p', M.Small p → M.Small p' → M.Small (p + p') ∧ M.Small (-p)) ∧ (∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]), ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧ ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p)) ∧ (∀ p, PrimeTo d q p → M.Small p → InOK d p) ∧ ∀ (p α s : ℂ), InOK d α → α ≠ 0 → PrimeTo d q s → InOK d (α * p + s - 1 / 2) → M.Small p → q ≠ 2 ∧ InOK d (s - 1 / 2) := by
  intro d q hq M ω hd hd16 hsp hL hM
  obtain ⟨hadd, hcm⟩ := GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω hM
  obtain ⟨hex, hex', huniq, hlat, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω hM
  obtain ⟨⟨-, -, hring⟩, halg, -, -, hhalf, -, -⟩ := okArith d q M.ι hd hd16 hsp
  have iadd : ∀ {a b}, InOK d a → InOK d b → InOK d (a + b) := fun ha hb => (hring _ _ ha hb).1
  have imul : ∀ {a b}, InOK d a → InOK d b → InOK d (a * b) := fun ha hb => (hring _ _ ha hb).2.1
  have iconj : ∀ {a}, InOK d a → InOK d (conj a) := fun ha => (hring _ _ ha ha).2.2.2
  have one_iff : ∀ p, M.At ω 1 p ↔ InOK d p := by
    intro p
    rw [hlat 1 0 p h10, zero_sub, neg_mem_iff, hL]
  have hpow : ∀ ζ p (N : ℕ), M.At ω ζ p → M.At ω (ζ ^ N) ((N : ℂ) * p) := by
    intro ζ p N h
    induction N with
    | zero => simpa using h10
    | succ N ih =>
      have := hadd _ _ _ _ ih h
      rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact this
  have htors : ∀ ζ p (N : ℕ), M.At ω ζ p → InOK d ((N : ℂ) * p) → ζ ^ N = 1 :=
    fun ζ p N h hN => huniq _ _ _ (hpow ζ p N h) ((one_iff _).2 hN)
  have h2 : ∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]),
      ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧
        ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p) := by
    intro p N hN hNp hp
    obtain ⟨ζ, hζ⟩ := hex' p hp
    obtain ⟨n, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.out.ne_one
    have hm' : Nat.Coprime m q := ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hm).symm
    have hz : ζ ^ (q ^ n) = 1 := by
      refine eq_one_of_pow (norm_pow_sub_one hζ.2.1 _) hm' ?_
      rw [← pow_mul]; exact htors _ _ _ hζ hNp
    refine ⟨n, ζ, hz, hζ, fun α hα hn => ?_⟩
    obtain ⟨⟨a, ha⟩, -⟩ := halg α hα
    have := hcm α a n 0 ζ p (fun l hl => (hL _).2 (imul hα ((hL _).1 hl))) ha
      (by rw [ha, norm_zc'] at hn; simpa using hn) hz hζ
    rw [pow_zero] at this
    exact (one_iff _).1 this
  refine ⟨?_, h2, ?_, ?_⟩
  · intro p p' hp hp'
    obtain ⟨ζ, hζ⟩ := hex' p hp
    obtain ⟨ζ', hζ'⟩ := hex' p' hp'
    refine ⟨(hadd _ _ _ _ hζ hζ').1, ?_⟩
    have hn : ‖ζ‖ = 1 := norm_eq_one hζ.2.1
    have h0 : ζ ≠ 0 := by rintro rfl; simp at hn
    have hinv : ‖ζ⁻¹ - 1‖ < 1 := by
      have : ζ⁻¹ - 1 = -(ζ⁻¹ * (ζ - 1)) := by field_simp; ring
      rw [this, norm_neg, norm_mul, norm_inv, hn, inv_one, one_mul]; exact hζ.2.1
    obtain ⟨r, hr⟩ := hex _ hinv
    have h3 := hadd _ _ _ _ hr hζ
    rw [inv_mul_cancel₀ h0, one_iff, ← hL] at h3
    exact ((hlat _ r (-p) hr).2 (by rwa [sub_neg_eq_add])).1
  · rintro p ⟨s, -, hsq, hsp⟩ hp
    obtain ⟨ζ, hζ⟩ := hex' p hp
    have := eq_one_of_pow hζ.2.1 hsq (htors _ _ _ hζ hsp)
    subst this
    exact (one_iff _).1 hζ
  · rintro p α s hα hα0 ⟨t, ht, htq, hts⟩ hin hp
    obtain ⟨-, ⟨N, hN⟩, -⟩ := halg α hα
    have hN0 : N ≠ 0 := by
      rintro rfl
      have : α * conj α = 0 := by simpa using hN.symm
      rcases mul_eq_zero.1 this with h | h
      · exact hα0 h
      · exact hα0 (by simpa using h)
    have h2t : InOK d (((2 * t : ℕ) : ℂ) * (s - 1 / 2)) :=
      inOK_of_eq (iadd (imul (inOK_int d 2) hts) (inOK_int d (-t))) (by push_cast; ring)
    have hNp : InOK d (((2 * t * N : ℕ) : ℂ) * p) := by
      refine inOK_of_eq (imul (iconj hα) (iadd (imul (inOK_int d (2 * t)) hin)
        (imul (inOK_int d (-1)) h2t))) ?_
      push_cast; rw [hN]; ring
    obtain ⟨n, ζ, -, -, hk⟩ := h2 p _ (by positivity) hNp hp
    have hβ : ∀ β, InOK d β → ‖M.ι β‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (β * (s - 1 / 2)) := by
      intro β hβ hn
      refine inOK_of_eq (iadd (imul hβ hin) (imul (inOK_int d (-1)) (imul hα (hk β hβ hn)))) ?_
      push_cast; ring
    have hq2 : q ≠ 2 := by
      intro h
      obtain ⟨β, hβ1, hβ2, hβ3⟩ := hhalf n
      apply hβ3
      have hodd : Odd t := by
        rw [h] at htq; exact Nat.coprime_two_right.1 htq
      obtain ⟨k, hk'⟩ := hodd
      have hk2 : (t : ℂ) = 2 * k + 1 := by exact_mod_cast hk'
      refine inOK_of_eq (iadd (iadd (imul hβ1 hts) (imul (inOK_int d (-t)) (hβ β hβ1 hβ2)))
        (imul (inOK_int d (-k)) hβ1)) ?_
      push_cast; rw [hk2]; ring
    refine ⟨hq2, ?_⟩
    have hc : Nat.Coprime (2 * t) (q ^ n) := by
      refine Nat.Coprime.pow_right n (Nat.Coprime.mul_left ?_ htq)
      exact (Nat.coprime_primes Nat.prime_two hq.out).2 hq2.symm
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
    have hab' : (a : ℂ) * ((2 * t : ℕ) : ℂ) + b * (q : ℂ) ^ n = 1 := by exact_mod_cast hab
    have h3 := hβ ((q : ℂ) ^ n) (inOK_of_eq (inOK_int d (q ^ n)) (by push_cast; rfl))
      (by rw [map_pow, map_natCast, norm_q_pow])
    refine inOK_of_eq (iadd (imul (inOK_int d a) h2t) (imul (inOK_int d b) h3)) ?_
    linear_combination (s - 1 / 2) * hab'

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SprimeNonnegTwo
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

set_option autoImplicit false

namespace GlobalTheory.RunDepth

theorem sprime_nonneg_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ), O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) → PiSplit (H := H) Dd → LeafPage O → ∀ v : HeightOneSpectrum (𝓞 K), plc v ∈ O.sm → ∀ j, 0 ≤ DepthTie.s1T Xo c Dd O ι v j := by
  intro E _ _ _ H l Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι hT hpr hσ hsp hPg v hv j
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg1p, hg2p, hq1p, hdp, -, -, -, -, -, -, hg1t, hg2t, -, -, -⟩ := hPg
  obtain ⟨h1, h2, h3, h4, h5⟩ := hpr
  have hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime :=
    ⟨h1 ▸ hg1p, h2 ▸ hg2p, h3 ▸ hq1p, h4 ▸ hdp⟩
  have hn1 : plc v ≠ Dd.Q.g1 := by
    rw [← h1]; exact fun h => hg1t (h ▸ hv)
  have hn2 : plc v ≠ Dd.Q.g2 := by
    rw [← h2]; exact fun h => hg2t (h ▸ hv)
  have hs : DepthTie.sWT Xo c Dd ι v j = (Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v) : ℝ) := by
    unfold DepthTie.sWT DepthTie.nuT DepthTie.nuWT nuStarAt DepPage.nuN DepthTie.e2
    rw [DepthTie.resChar_below (F := c.F) v, if_neg hn1, if_neg hn2]
    ring
  set N := DepthTie.Nsig Dd.Q (DF (Dw (ι j)) (Dd.aL (ι j))) (DF (Dw (ι j)) (Dd.aF (ι j))) with hNdef
  have hN : N ≠ 0 := DepthTie.Nsig_ne_zero Dd.Q hprime _ _
  have : Fact (plc v).Prime := ⟨plc_prime v⟩
  have hdvd : (plc v) ^ ((Dd.Q.T : ℕ) * Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v)) ∣ N := by
    rw [hNdef]
    unfold DepthTie.Nsig DepPage.Z1
    refine Dvd.dvd.mul_left ?_ _
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((pow_dvd_pow _ (Nat.le_add_right _ _)).trans
      (Finset.dvd_prod_of_mem (fun p => p ^ ((Dd.Q.T : ℕ) * Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) p + Dd.Q.cP (DF (Dw (ι j)) (Dd.aF (ι j))) p))
        (Finset.mem_filter.2 ⟨h5 ▸ hv, plc_prime v⟩))) _) _
  have hle : ((Dd.Q.T : ℕ) : ℝ) * (Dd.Q.cP (DF (Dw (ι j)) (Dd.aL (ι j))) (plc v) : ℝ) ≤
      (padicValNat (plc v) N : ℝ) := by
    exact_mod_cast (padicValNat_dvd_iff_le hN).1 hdvd
  have hnn0 : (0 : ℝ) ≤ (vw v (nnKAt (H := H) (LL := K) Dd (ι j)) : ℝ) := by
    exact_mod_cast DepthTie.vw_nonneg_of_isIntegral v _ (DepthTie.nnK_isIntegral Dd (ι j))
  have he := ramw_pos v
  unfold DepthTie.s1T
  rw [hs, hσ v j, DepthTie.vw_sig Dd hsp hprime v, add_div, mul_div_cancel_right₀ _ he.ne', hT]
  have : 0 ≤ (vw v (nnKAt (H := H) (LL := K) Dd (ι j)) : ℝ) / (ramw v : ℝ) := div_nonneg hnn0 he.le
  linarith

end GlobalTheory.RunDepth
end

