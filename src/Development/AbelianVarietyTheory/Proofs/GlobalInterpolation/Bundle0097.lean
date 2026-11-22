import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0015
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RingHomEqOfComapEqUnramifiedDegreeOne
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem ringHom_eq_of_comap_eq_unramified_degree_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (φ ψ : E →+* K)
    (w : HeightOneSpectrum (𝓞 K)) (Q : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime)
    (hN : Ideal.absNorm Q.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2)
    (hφ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal)
    (hψ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom ψ r ∈ w.asIdeal) :
    φ = ψ := by
  set f := RingOfIntegers.mapRingHom φ with hf
  set g := RingOfIntegers.mapRingHom ψ with hg
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal := hN ▸ Ideal.absNorm_mem Q.asIdeal
  have hQp := Q.isPrime

  have h1 : ∀ x : 𝓞 E, ∃ a : ℤ, x - (a : 𝓞 E) ∈ Q.asIdeal := by
    intro x
    haveI : Fact p.Prime := ⟨hp⟩
    have hc : Nat.card (𝓞 E ⧸ Q.asIdeal) = p := by
      rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := mem_zmultiples_of_prime_card (g := (1 : 𝓞 E ⧸ Q.asIdeal))
      (g' := Ideal.Quotient.mk Q.asIdeal x) hc one_ne_zero
    obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.1 h
    refine ⟨a, Ideal.Quotient.eq.1 ?_⟩
    rw [← ha, map_intCast, zsmul_one]
  have h2 : Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 = Q.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := Q.asIdeal) (i := 1)
      (I := Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2) Q.ne_bot ?_ ?_
    · simpa using h
    · refine lt_of_le_of_ne le_sup_right fun h => hsq ?_
      have h' : ((p : ℕ) : 𝓞 E) ∈ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 :=
        Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      rw [← h] at h'
      exact h'
    · rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hpQ) (Ideal.pow_le_self two_ne_zero)
  have h3 : ∀ n : ℕ, Q.asIdeal ≤ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rcases n with _ | n
      · simp
      refine h2.ge.trans (sup_le le_sup_left ?_)
      rw [sq]
      refine (Ideal.mul_mono_right ih).trans ?_
      rw [Ideal.mul_sup, ← pow_succ']
      exact sup_le_sup_right Ideal.mul_le_right _
  have hmap : ∀ (k : 𝓞 E →+* 𝓞 K), (∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ k r ∈ w.asIdeal) →
      ∀ (n : ℕ) (z : 𝓞 E), z ∈ Q.asIdeal ^ n → k z ∈ w.asIdeal ^ n := by
    intro k hk n z hz
    have h := Ideal.mem_map_of_mem k hz
    rw [Ideal.map_pow] at h
    refine Ideal.pow_right_mono ?_ n h
    exact Ideal.map_le_iff_le_comap.2 fun r hr => (hk r).1 hr
  have hpw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    simpa using (hφ _).1 hpQ
  have h4 : ∀ (n : ℕ) (x : 𝓞 E), f x - g x ∈ w.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := h1 x
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h3 (n + 1) ha)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have hx : x = c * p + z + a := by rw [hyz]; ring
      have he : f x - g x = (f c - g c) * p + (f z - g z) := by
        rw [hx]; simp only [map_add, map_mul, map_natCast, map_intCast]; ring
      rw [he]
      refine add_mem ?_ (sub_mem (hmap f hφ _ _ hz) (hmap g hψ _ _ hz))
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih c) hpw
  have h5 : ∀ x : 𝓞 E, f x = g x := by
    intro x
    have hb := Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top
    have : f x - g x ∈ (⊥ : Ideal (𝓞 K)) := by
      rw [← hb]; exact Ideal.mem_iInf.2 fun n => h4 n x
    exact sub_eq_zero.1 (Ideal.mem_bot.1 this)
  refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
  exact congrArg (algebraMap (𝓞 K) K) (h5 x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SamePointOfSameScale
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.TieSame

theorem bsH_val_congr {e e' : Formalism.HC.Frame} (he : e = e') (h t : e.A) (h' t' : e'.A)
    (hh : h.val = h'.val) (ht : t.val = t'.val) : (Arith.bsH h t).val = (Arith.bsH h' t').val := by
  subst he
  have h1 := Formalism.HC.Frame.A.val_injective _ hh
  have h2 := Formalism.HC.Frame.A.val_injective _ ht
  rw [h1, h2]

theorem mem_iff_val_mem {e : Formalism.HC.Frame} (T : Finset e.A) (t : e.A) :
    t ∈ T ↔ t.val ∈ T.image Formalism.HC.Frame.A.val := by
  constructor
  · intro h; exact Finset.mem_image_of_mem _ h
  · intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    rwa [← Formalism.HC.Frame.A.val_injective _ hst]

theorem kapISet_congr {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hR : D.R = D'.R) (hs : L.sc = L'.sc) (hS : L.Sc = L'.Sc)
    (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = G.kapISet L' K p n' TT a b := by
  have hk : D.R.k = D'.R.k := by rw [hR]
  have hc : G.cG L = G.cG L' := by unfold G.cG; rw [hS]
  have hD : G.DIf K L p n' = G.DIf K L' p n' := by unfold G.DIf; rw [hs, hk]
  have h6 : G.c6f K L p n' = G.c6f K L' p n' := by unfold G.c6f; rw [hD, hs, hk, hc]
  have ht : G.tIf K L p n' TT a b = G.tIf K L' p n' TT a b := by unfold G.tIf; rw [h6, hs, hk, hc]
  unfold G.kapISet
  rw [hc, hD, ht, hk]

theorem nonempty_place (D : D7) : Nonempty D.what₂.places.Pl := by
  haveI := D.nfLL
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.what₂.LL)
  exact ⟨D.plEq.symm ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem off_lift {C : FC} {cD ch : ℝ} (p : Pt C) (hv : Val C cD ch p.L) (j : ℕ) (hj : j ∈ SizeData₂.lifts p.D) (t : G.HH p.D) :
    p.ta.Gx.off j (false, t) =
      (if t ∈ p.D.host.TT then ((⌊p.L.sc.b' / p.L.sc.x⌋ : ℤ) : ℝ) else ((⌈p.L.sc.w'' p.D.R.n⌉ : ℤ) : ℝ)) +
        ((j - 1 : ℕ) : ℝ) * (h0v p.L.sc ch : ℝ) + (h0v p.L.sc ch : ℝ) / 2 := by
  obtain ⟨w⟩ := nonempty_place p.D
  have hP := factPlaces p.D.R.toFrame
  have hmem : p.D.R.tau1 t ∈ p.D.R.Psi := (hP.1 _).2 (Or.inl ⟨t, rfl⟩)
  set τ := p.D.eTau.symm ⟨_, hmem⟩ with hτ
  have hτe : (p.D.eTau τ : p.D.R.GG) = p.D.R.tau1 t := by rw [hτ, Equiv.apply_symm_apply]
  have hf := (p.ta.fills w).1 j hj τ (false, t) (by rw [hτe]; rfl)
  have hjm : j - 1 < p.D.R.m := by
    have := Finset.mem_Icc.1 hj
    omega
  obtain ⟨-, -, ⟨b1, hb, htop, -, hthin⟩, -⟩ := hv.hc
  obtain ⟨hb1, hb2⟩ := hb τ ⟨j - 1, hjm⟩
  unfold wj at hf
  rw [dif_pos hjm, hb2, hb1] at hf
  unfold G.fill at hf
  by_cases ht : t ∈ p.D.host.TT
  · have h1 := htop τ ⟨t, ht⟩ hτe
    rw [if_pos ⟨rfl, ht⟩, h1] at hf
    rw [if_pos ht]
    unfold G.bL at hf
    rw [dif_pos ht] at hf
    push_cast at hf ⊢
    linarith
  · have h1 := hthin τ (by
      show p.D.host.IsThin (p.D.eTau τ : p.D.R.GG)
      rw [hτe]
      refine ⟨hmem, ?_, ?_⟩
      · intro h
        obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
        have : s = t := p.D.R.iota_bijective.1 (congrArg Prod.snd hst)
        exact ht (this ▸ hs)
      · intro h
        obtain ⟨s, -, hst⟩ := Finset.mem_image.1 h
        exact hP.2 _ _ hst.symm)
    rw [if_neg (fun h => ht h.2), h1] at hf
    rw [if_neg ht]
    push_cast at hf ⊢
    linarith

theorem same_of_from : ∀ (C : FC) (cD ch : ℝ) (p p' : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 u0' : ℕ), p.L.sc = p'.L.sc → Val C cD ch p.L → Val C cD ch p'.L → p.From H a b c u0 → p'.From H a b c u0' → CanonInst p.ta.Gx → CanonInst p'.ta.Gx → p.Same p' := by
  intro C cD ch p p' R H a b M c u0 u0' hs hv hv' hF hF' hC hC'
  have hQS := hF.QS_eq.trans hF'.QS_eq.symm
  have hart := hF.art_eq.trans hF'.art_eq.symm
  have hrd := hF.rd_eq.trans hF'.rd_eq.symm
  obtain ⟨hR, hTT, hT2, hq, hd, hg, hp1, hp2, -, -, hh, hw, -⟩ := hF
  obtain ⟨hR', hTT', hT2', hq', hd', hg', hp1', hp2', -, -, hh', hw', -⟩ := hF'
  have hRR : p.D.R = p'.D.R := hR.trans hR'.symm
  have hT : p.D.host.TT.image Formalism.HC.Frame.A.val = p'.D.host.TT.image Formalism.HC.Frame.A.val := hTT.trans hTT'.symm
  have hSc : p.L.Sc = p'.L.Sc := by rw [p.L.Sc_eq, p'.L.Sc_eq, hv.Del_eq, hv'.Del_eq, hs, hRR]
  have hmem : ∀ (t : G.HH p.D) (t' : G.HH p'.D), t.val = t'.val → (t ∈ p.D.host.TT ↔ t' ∈ p'.D.host.TT) := by
    intro t t' htt
    rw [mem_iff_val_mem p.D.host.TT t, mem_iff_val_mem p'.D.host.TT t', hT, htt]
  have hn : p.D.R.n = p'.D.R.n := by rw [hRR]
  refine ⟨hRR, hT, hT2.trans hT2'.symm, hq.trans hq'.symm, hd.trans hd'.symm, hg.trans hg'.symm, hp1.trans hp1'.symm,
    hp2.trans hp2'.symm, ?_, hSc, fun l => (hh l).trans (hh' l).symm, ?_, ?_, ?_, ?_, ?_, hQS, hart, hrd⟩
  · rw [hv.eta_eq, hv'.eta_eq, hs, hRR]
  · intro h t h' t' e1 e2
    rw [hC.1, hC'.1]
    exact bsH_val_congr (by rw [hRR]) h t h' t' e1 e2
  · intro j t t' htt
    have hm := hmem t t' htt
    have hl : SizeData₂.lifts p.D = SizeData₂.lifts p'.D := by unfold SizeData₂.lifts; rw [hRR]
    by_cases hj : j ∈ SizeData₂.lifts p.D
    · rw [off_lift p hv j hj t, off_lift p' hv' j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
    · rw [hC.2 j hj t, hC'.2 j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
  · funext l n' TT a' b'
    rw [p.xa.ex.kapI_def l n' TT a' b', p'.xa.ex.kapI_def l n' TT a' b', kapISet_congr p.L p'.L hRR hs hSc]
  · funext l
    rw [p.xa.ex.ep_def l, p'.xa.ex.ep_def l, hs, hRR]
  · intro t t' htt
    have hlt : (t : p.D.R.A).val < R.ord := by
      have := Formalism.HC.Frame.A.val_lt (t : p.D.R.A)
      rwa [show R.ord = p.D.R.ord by rw [hR]]
    have hv0 : (R.ofNat (t : p.D.R.A).val).val = (t : p.D.R.A).val :=
      R.toFrame.val_ofNat_of_lt hlt
    obtain ⟨e1, e2⟩ := hw t _ hv0.symm
    obtain ⟨e3, e4⟩ := hw' t' _ (htt.symm.trans hv0.symm)
    exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩

end GlobalTheory.EX.TieSame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SpanImageLeOf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.IdealTransport

section General

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
  (φ : R ≃+* R') (f : M ≃+ M') (h : ∀ r m, f (r • m) = φ r • f m)

include h

theorem span_image_le_of (N : Submodule R M) (N' : Submodule R' M') (S : Set M) (hS : N = Submodule.span R S)
    (hN : ∀ m ∈ S, f m ∈ N') : Submodule.span R' (f '' (N : Set M)) ≤ N' := by
  rw [Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  show f m ∈ N'
  have hm' : m ∈ Submodule.span R S := hS ▸ hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem x hx => exact hN x hx
  | zero => rw [map_zero]; exact N'.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact N'.add_mem hx hy
  | smul r x _ hx => rw [h]; exact N'.smul_mem _ hx

theorem span_image_span (S : Set M) :
    Submodule.span R' (f '' (Submodule.span R S : Set M)) = Submodule.span R' (f '' S) := by
  apply le_antisymm
  · exact span_image_le_of φ f h _ _ S rfl fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem mem_span_image (N : Submodule R M) (x : M') :
    x ∈ Submodule.span R' (f '' (N : Set M)) ↔ f.symm x ∈ N := by
  have hsm : ∀ (r : R') (y : M'), f.symm (r • y) = φ.symm r • f.symm y := by
    intro r y
    apply f.injective
    rw [h, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      simpa using hm
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact N.add_mem hy hz
    | smul r y _ hy => rw [hsm]; exact N.smul_mem _ hy
  · intro hx
    exact Submodule.subset_span ⟨f.symm x, hx, by simp⟩

end General

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E')

theorem map_smul_int (r : 𝓞 E) (x : E) : e (r • x) = RingOfIntegers.mapRingEquiv e r • e x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

abbrev trI (I : Submodule (𝓞 E) E) : Submodule (𝓞 E') E' := Submodule.span (𝓞 E') (e '' (I : Set E))

abbrev trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E') (Fin n → E') :=
  Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) => e (x i)) '' (N : Set (Fin n → E)))

theorem mem_trI (I : Submodule (𝓞 E) E) (x : E') : x ∈ trI e I ↔ e.symm x ∈ I := mem_span_image (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) I x

theorem trI_span (S : Set E) : trI e (Submodule.span (𝓞 E) S) = Submodule.span (𝓞 E') (e '' S) := span_image_span (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) S

theorem mem_trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E') :
    x ∈ trL e N ↔ (fun i => e.symm (x i)) ∈ N := mem_span_image (RingOfIntegers.mapRingEquiv e) (AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv)
    (fun r v => funext fun i => map_smul_int e r (v i)) N x

theorem trI_mul (I J : Submodule (𝓞 E) E) : trI e (I * J) = trI e I * trI e J := by
  rw [Submodule.mul_eq_span_mul_set I J, trI_span, Set.image_mul]
  exact (Submodule.span_mul_span _ _ _).symm

theorem trI_singleton (y : E) : trI e (Submodule.span (𝓞 E) {y}) = Submodule.span (𝓞 E') {e y} := by
  rw [trI_span, Set.image_singleton]

theorem trI_one : trI e 1 = 1 := by
  conv_lhs => rw [Submodule.one_eq_span]
  rw [trI_singleton, map_one, ← Submodule.one_eq_span]

theorem trI_surj (J : Submodule (𝓞 E') E') : ∃ I, trI e I = J := by
  refine ⟨Submodule.span (𝓞 E) (e.symm '' (J : Set E')), ?_⟩
  rw [trI_span, Set.image_image]
  simp only [RingEquiv.apply_symm_apply, Set.image_id']
  exact Submodule.span_eq J

theorem mem_one_iff (x : E') : x ∈ (1 : Submodule (𝓞 E') E') ↔ e.symm x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← trI_one e, mem_trI]

theorem map_mulVec' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (A.map e).mulVec (fun i => e (v i)) = fun i => e (A.mulVec v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem det_map' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : (A.map e).det = e A.det := (RingHom.map_det (e : E →+* E') A).symm

theorem carries_iff {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) :
    (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')), (A.map e).mulVec v ∈ trL e N) ↔
      ∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)), A.mulVec v ∈ N := by
  constructor
  · intro H v hv
    have hv' : (fun i => e (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [mem_one_iff e, RingEquiv.symm_apply_apply]
      exact hv i hi
    have hA := H _ hv'
    rw [map_mulVec' e A v, mem_trL] at hA
    simpa using hA
  · intro H v hv
    have hv' : (fun i => e.symm (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [← mem_one_iff e]
      exact hv i hi
    have hmv : (A.map e).mulVec v = fun i => e (A.mulVec (fun i => e.symm (v i)) i) := by
      have hk := map_mulVec' e A (fun i => e.symm (v i))
      simp only [RingEquiv.apply_symm_apply] at hk
      exact hk
    rw [hmv, mem_trL]
    simpa using H _ hv'

theorem det_set {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) :
    {x | ∃ A : Matrix (Fin n) (Fin n) E', (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')),
        A.mulVec v ∈ trL e N) ∧ x = A.det} =
      e '' {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)),
        A.mulVec v ∈ N) ∧ x = A.det} := by
  ext x
  constructor
  · rintro ⟨A', hA', rfl⟩
    have hmap : (A'.map e.symm).map e = A' := by
      ext i j
      simp
    refine ⟨(A'.map e.symm).det, ⟨A'.map e.symm, ?_, rfl⟩, ?_⟩
    · rw [← carries_iff e N, hmap]
      exact hA'
    · rw [← det_map', hmap]
  · rintro ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map e, (carries_iff e N A).mpr hA, (det_map' e A).symm⟩

end Fields

theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X), (∀ (I : Submodule (𝓞 X.E) X.E) (x : D.host.E), x ∈ idTo s I ↔ s.iE.symm x ∈ I) ∧ (∀ I J : Submodule (𝓞 X.E) X.E, idTo s (I * J) = idTo s I * idTo s J) ∧ idTo s 1 = 1 ∧ (∀ y : X.E, idTo s (Submodule.span (𝓞 X.E) {y}) = Submodule.span (𝓞 D.host.E) {s.iE y}) ∧ (∀ 𝔞 : TaylorLogMetric.IdE D, ∃ I, idTo s I = 𝔞) ∧ ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = idTo s (detLat N) := by
  intro D X s
  refine ⟨fun I x => mem_trI s.iE I x, fun I J => trI_mul s.iE I J, trI_one s.iE,
    fun y => trI_singleton s.iE y, trI_surj s.iE, fun n N => ?_⟩
  calc TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)
      = Submodule.span (𝓞 D.host.E) (s.iE '' {x | ∃ A : Matrix (Fin n) (Fin n) X.E,
          (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 X.E) X.E)), A.mulVec v ∈ N) ∧
            x = A.det}) := by
        rw [← det_set s.iE N]
        rfl
    _ = idTo s (detLat N) := (trI_span s.iE _).symm

end GlobalTheory.IdealTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubAddLeSpread
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

namespace GlobalTheory.KerT

theorem sub_add_le_spread {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    lam.w a - lam.w b + (N : ℤ) ≤ lam.spread := by
  have hN : 0 < N := a.pos
  have h1 : lam.w a ≤ lam.w ⟨0, hN⟩ := lam.anti (Fin.le_def.2 (Nat.zero_le _))
  have h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w b := lam.anti (Fin.le_def.2 (by have := b.2; simp only; omega))
  unfold DomWeight.spread
  rw [dif_pos hN]
  linarith

theorem alcoveAt_of_ok : ∀ (Z : Dat), Z.Ok → ∀ (u : Z.Pr.Word) (j : ℕ), j ≤ Z.R.m → AlcoveAt Z.W u j := by
  intro Z hZ u j hj τ a b
  have h1 := hZ.sizes.two_spread_lt u j hj τ
  have h2 := sub_add_le_spread (Z.W.lamTrue u j τ) a b
  linarith

end GlobalTheory.KerT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCloudUnitLower
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem cloudUnit_poly_bounds (x c F K cD k m N f L : ℝ) (hx : 1 ≤ x) (hc : 1 ≤ c) (hcx : c ≤ x) (hF : 1 ≤ F)
    (hK : 1 ≤ K) (hcD : 5 * c + F * c + 406 * K + 412 ≤ cD)
    (hk0 : 0 ≤ k) (hk : k ≤ x ^ (5 : ℝ)) (hm0 : 0 ≤ m) (hm : m ≤ x) (hN0 : 0 ≤ N) (hN : N ≤ x ^ (402 : ℝ))
    (hf0 : 0 ≤ f) (hf : f ≤ x ^ (3 : ℝ)) (hL0 : 0 ≤ L) (hL : L ≤ x) :
    (k ^ c * (c * m) ^ 3 / (6 * x ^ (-F)) ^ c ≤ x ^ cD ∧ c * m * N ≤ x ^ cD ∧
      k ^ c * (c * m ^ 4 * L) ^ 4 ≤ x ^ cD ∧ N * m ^ 10 ≤ x ^ cD) ∧ (N * f * L) ^ K ≤ x ^ cD := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hFc : 0 ≤ F * c := by positivity
  have mono : ∀ a : ℝ, a ≤ 5 * c + F * c + 406 * K + 412 → x ^ a ≤ x ^ cD := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx (ha.trans hcD)
  have hkc : k ^ c ≤ x ^ (5 * c) := by
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow hk0 hk hc0
  have hnat : ∀ n : ℕ, x ^ n = x ^ (n : ℝ) := fun n => (Real.rpow_natCast x n).symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have h1 : (c * m) ^ 3 ≤ x ^ (6 : ℝ) := by
      calc (c * m) ^ 3 ≤ (x * x) ^ 3 := by gcongr
        _ = x ^ (6 : ℕ) := by ring
        _ = x ^ (6 : ℝ) := by rw [hnat]; norm_num
    have hp : 0 < x ^ (-F) := Real.rpow_pos_of_pos hx0 _
    have h2 : x ^ (-(F * c)) ≤ (6 * x ^ (-F)) ^ c := by
      rw [← neg_mul, Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow hp.le (by linarith) hc0
    have hq : 0 < x ^ (-(F * c)) := Real.rpow_pos_of_pos hx0 _
    calc k ^ c * (c * m) ^ 3 / (6 * x ^ (-F)) ^ c ≤ x ^ (5 * c) * x ^ (6 : ℝ) / x ^ (-(F * c)) := by gcongr
      _ = x ^ (5 * c + 6 + F * c) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0]; congr 1; ring
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc c * m * N ≤ x * x * x ^ (402 : ℝ) := by gcongr
      _ = x ^ (2 : ℕ) * x ^ (402 : ℝ) := by ring
      _ = x ^ (404 : ℝ) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc k ^ c * (c * m ^ 4 * L) ^ 4 ≤ x ^ (5 * c) * (x * x ^ 4 * x) ^ 4 := by gcongr
      _ = x ^ (5 * c) * x ^ (24 : ℕ) := by ring
      _ = x ^ (5 * c + 24) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · calc N * m ^ 10 ≤ x ^ (402 : ℝ) * x ^ 10 := by gcongr
      _ = x ^ (412 : ℝ) := by rw [hnat, ← Real.rpow_add hx0]; norm_num
      _ ≤ x ^ cD := mono _ (by linarith)
  · have h1 : N * f * L ≤ x ^ (406 : ℝ) := by
      calc N * f * L ≤ x ^ (402 : ℝ) * x ^ (3 : ℝ) * x := by gcongr
        _ = x ^ (406 : ℝ) := by
          rw [← Real.rpow_add hx0, ← Real.rpow_add_one hx0.ne']; norm_num
    calc (N * f * L) ^ K ≤ (x ^ (406 : ℝ)) ^ K := Real.rpow_le_rpow (by positivity) h1 (by linarith)
      _ = x ^ (406 * K) := by rw [← Real.rpow_mul hx0.le]
      _ ≤ x ^ cD := mono _ (by linarith)

theorem szRow_cloudUnit_lower : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * D.R.m) ^ 3 / D.div.etaF ^ C.P.CDel ≤ (D.s.Del : ℝ) ∧ C.P.CDel * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧ (D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * (D.R.m : ℝ) ^ 4 * L.sc.L) ^ 4 ≤ (D.s.Del : ℝ) ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ)) ∧ (((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ (D.s.Del : ℝ))) := by
  intro eps h0 h1 C hC
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmid, hlast⟩ := hC
  have hF : 1 ≤ C.P.CF := hmid _ (by simp [FC.cMid])
  have hc : 1 ≤ C.P.CDel := hlast _ (by simp [FC.cLast])
  have hK : 1 ≤ C.P.CCount := hlast _ (by simp [FC.cLast])
  refine ⟨5 * C.P.CDel + C.P.CF * C.P.CDel + 406 * C.P.CCount + 412, fun cD hcD => ⟨0, fun ch _ =>
    ⟨max x0 C.P.CDel, fun D L he hx V => ?_⟩⟩⟩
  have hxc : C.P.CDel ≤ L.sc.x := (le_max_right _ _).trans hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ :=
    hx0 L.sc D.R he ((le_max_left _ _).trans hx) V.ranks
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hDel : L.sc.x ^ cD ≤ (D.s.Del : ℝ) := by
    rw [V.Del_eq, Rat.cast_natCast]
    exact Nat.le_ceil _
  obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := cloudUnit_poly_bounds L.sc.x C.P.CDel C.P.CF C.P.CCount cD D.R.k D.R.m
    (D.R.N D.R.m) D.R.f L.sc.L (hc.trans hxc) hc hxc hF hK hcD (Nat.cast_nonneg _) hk (Nat.cast_nonneg _) hm
    (Nat.cast_nonneg _) hN (Nat.cast_nonneg _) hf (by linarith) hL
  rw [← V.etaF_eq] at a1
  exact ⟨⟨a1.trans hDel, a2.trans hDel, a3.trans hDel, a4.trans hDel⟩, a5.trans hDel⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeKRelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeKRel : SzRow (fun _ _ L => SizeKRel L) := by
  first | exact @GlobalTheory.EX.szRow_sizeKRel | exact GlobalTheory.EX.szRow_sizeKRel | (intros; apply GlobalTheory.EX.szRow_sizeKRel <;> assumption)
end

