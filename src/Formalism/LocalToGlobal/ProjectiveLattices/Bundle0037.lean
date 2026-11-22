import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.DepRun
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem satDir_of (hS : ChartSaturated Xo c) {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntChart T io y) :
    SatDir T (letI := io.toAlgebra; C.ch.uvec) := by
  intro τ
  obtain ⟨⟨w, emb, hw, hbasis⟩, -⟩ := hS T io y C τ
  have huv := C.gen.1.2.2.2.2.2.2
  choose A hA using fun m : Fin (chD C.ch) => (hbasis (Pi.single m 1)).exists
  have hAw : (Matrix.of A) * (Matrix.of w) = 1 := by
    ext m j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [hA m j, Pi.single_apply]
    by_cases hjm : j = m
    · subst hjm; simp
    · simp [hjm, Ne.symm hjm]
  have hwA : (Matrix.of w) * (Matrix.of A) = 1 := by
    first
      | exact mul_eq_one_comm.mp hAw
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hAw
  refine ⟨fun i j => A j (emb i), fun i i' => ?_⟩
  letI := io.toAlgebra
  have e1 : ∀ j, C.ch.uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (A j (emb i)) =
      algebraMap T.V T.Fr (w (emb i') j * A j (emb i)) := by
    intro j
    rw [huv, map_mul, hw]
  refine (Finset.sum_congr rfl (fun j _ => e1 j)).trans ?_
  rw [← map_sum]
  have h3 := congrFun (congrFun hwA (emb i')) (emb i)
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h3
  rw [h3]
  by_cases hii : i' = i
  · subst hii; simp
  · rw [if_neg (fun h' => hii (emb.injective h')), if_neg hii, map_zero]

theorem nuW_le_crude (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n) :
    nuW Xo c la k a n ≤ max 0 (crudeBd la (DF Dw a) : EReal) := by
  unfold nuW
  refine max_le_max le_rfl ?_
  unfold nuSup
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho =>
    iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  unfold nuLoc
  refine (iInf_le _ C).trans ?_
  letI := io.toAlgebra
  exact (crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).1

omit [StarRing (𝓞 E)] in
theorem card_Lt1_le_finrank_mul : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc ∑ τ : E →+* ℂ, Dw.mult τ ≤ ∑ _τ : E →+* ℂ, (Dw.p + Dw.q) := by
        apply Finset.sum_le_sum
        intro τ _
        unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
        split_ifs <;> omega
    _ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
        rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, smul_eq_mul]

end

variable {D : D7}

theorem nuFinAt_of (T : Core D) (hp : T.Q.Pins) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)]
    (hw : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j)
    (hE : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c) (hS : ∀ j, InR D j → ChartSaturated (T.Q.Xo j) T.Q.c) :
    NuFinAt T Dd := by
  intro j hj la
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have hn : Fintype.card (Lt1 (T.Q.Dw j)) ≤ Dd.nW j := by
    refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]; exact (hw j hj).2
  refine ne_top_of_le_ne_top ?_ (nuW_le_crude (hE j hj) (hS j hj) la _ _ _ (fun τ i i' h => (hw j hj).1 τ h) hn)
  rcases le_total (0 : EReal) (crudeBd la (DF (T.Q.Dw j) (Dd.aL j)) : EReal) with h | h
  · rw [max_eq_right h]; exact EReal.coe_ne_top _
  · rw [max_eq_left h]; exact EReal.zero_ne_top

def depRun (T : Core D) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j) : DepData D.host.E :=
  depDataOf T EX Tn vd (fun j => wtA (wL j)) (fun j => wtA (wF j)) (fun j => (wL j).n)
    (fun j => ∑ τ, ∑ i, (ka j).aP τ i) fun j => ∑ τ, ∑ i, (ka j).aM τ i

theorem lawsPi_depRun [StarRing (𝓞 D.host.E)] {T : Core D} (h : LawsM T) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j)
    (hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (wL j).n) : LawsPi T (depRun T EX Tn vd wL wF ka) where
  page := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  tPos := tPos_depDataOf ..
  sm := rfl
  wts j hj := ⟨(dom_wtA (wL j)).1, hn j hj⟩
  piSplit := piSplit_depDataOf ..
  piHalf := piHalf_depDataOf _ _ _ _ _ _ _ _ _ h

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.MapRingEquivTransApply
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem host_ext {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (hd : H.d = H'.d) (hrt : H.rt = H'.rt)
    (hrt0 : H.rt0 = H'.rt0) : H = H' := by
  obtain ⟨d, _, _, rt, _, w0, tw, bar, be, _, rt0, _⟩ := H
  obtain ⟨d', _, _, rt', _, w0', tw', bar', be', _, rt0', _⟩ := H'
  simp only at hd hrt hrt0
  subst hd hrt hrt0
  have hw : w0 = w0' := by
    apply RingOfIntegers.ext
    have h2 := congrArg (fun x : 𝓞 E => (x : E)) (tw.trans tw'.symm)
    simp only [map_mul, map_ofNat] at h2
    exact mul_left_cancel₀ two_ne_zero h2
  have hb : bar = bar' := RingEquiv.ext fun a => RingOfIntegers.ext ((be a).trans (be' a).symm)
  subst hw hb
  rfl

theorem level_ext {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l l' : Level H} (hM : l.M = l'.M) (hMb : l.Mb = l'.Mb)
    (hA : l.A = l'.A) : l = l' := by
  obtain ⟨M, _, _, Mb, _, _, _, A, _⟩ := l
  obtain ⟨M', _, _, Mb', _, _, _, A', _⟩ := l'
  simp only at hM hMb hA
  subst hM hMb hA
  rfl

theorem coeff_ext {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c c' : Coeff l} (h : c.F = c'.F) : c = c' := by
  obtain ⟨F, _, _, _, _⟩ := c
  obtain ⟨F', _, _, _, _⟩ := c'
  simp only at h
  subst h
  rfl

end Ext

variable {D : D7}

namespace Par

theorem coe_mem_of_pinField {Q Q' : Par D} (h : Q.PinField) (h' : Q'.PinField) (a : 𝓞 Q.c.F) :
    ((a : Q.c.F) : ℂ) ∈ Q'.c.F := by
  have e1 := h a
  have e2 := h' (Q'.eO.symm (Q.eO a))
  rw [RingEquiv.apply_symm_apply] at e2
  rw [← e1, e2]
  exact SetLike.coe_mem _

theorem F_le {Q Q' : Par D} (h : Q.PinField) (h' : Q'.PinField) : Q.c.F ≤ Q'.c.F := by
  intro x hx
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨x, hx⟩ : Q.c.F)
  have hx' : x = ((algebraMap (𝓞 Q.c.F) Q.c.F a : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F b : Q.c.F) : ℂ) := by
    rw [← IntermediateField.coe_div, hab]
  rw [hx']
  exact div_mem (coe_mem_of_pinField h h' a) (coe_mem_of_pinField h h' b)

theorem F_eq {Q Q' : Par D} (h : Q.PinField) (h' : Q'.PinField) : Q.c.F = Q'.c.F :=
  le_antisymm (F_le h h') (F_le h' h)

end Par

open Classical in

def NlM {T : Core D} (h : LawsM T) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) : T.R j → ℝ :=
  if hj : InR D j then
    l2C (T.U j) (goodOf T.Q.c σ) (T.V j _) (T.dict j _) (T.mu j _) (xiR D) (wtA w) w.n
      (h.cuspidalL2Subspace j hj _ (goodEmb_goodOf _ σ) _ _ (dom_wtA w))
  else 0

structure IsCoreIso {T T' : Core D} (h : LawsM T) (h' : LawsM T') (j : ℕ) (fe : T.Q.c.F ≃+* T'.Q.c.F)
    (Φ : T.R j ≃+* T'.R j) (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)) : Prop where
  fe_coe : ∀ x, ((fe x : T'.Q.c.F) : ℂ) = x
  smul : ∀ (a : T.Q.c.F) (f : T.R j), Φ (a • f) = fe a • Φ f
  eO : ∀ x, T'.Q.eO (RingOfIntegers.mapRingEquiv fe x) = T.Q.eO x
  pl_bij : Function.Bijective pl
  pl_mem : ∀ la x, x ∈ la.asIdeal ↔ RingOfIntegers.mapRingEquiv fe x ∈ (pl la).asIdeal
  pl_norm : ∀ la, Ideal.absNorm (pl la).asIdeal = Ideal.absNorm la.asIdeal
  cusp : ∀ (w : WeightFamilies.Wt D j) (f : T.R j), f ∈ T.C j w ↔ Φ f ∈ T'.C j w
  vals : ∀ la (v : T.R j → EReal), v ∈ T.Vs j la ↔ v ∘ Φ.symm ∈ T'.Vs j (pl la)
  sup : ∀ (w : WeightFamilies.Wt D j) (σ : T'.Q.c.F →+* ℂ) (f : T.R j), f ∈ T.C j w →
    T'.Ns j w σ (Φ f) = T.Ns j w (σ.comp fe.toRingHom) f
  l2 : ∀ (w : WeightFamilies.Wt D j) (σ : T'.Q.c.F →+* ℂ) (f : T.R j), f ∈ T.C j w →
    NlM h' j w σ (Φ f) = NlM h j w (σ.comp fe.toRingHom) f

theorem mapRingEquiv_refl_apply {K : Type} [Field K] (x : 𝓞 K) : RingOfIntegers.mapRingEquiv (RingEquiv.refl K) x = x :=
  RingOfIntegers.ext rfl

theorem mapRingEquiv_trans_apply {K K' K'' : Type} [Field K] [Field K'] [Field K''] (e : K ≃+* K') (e' : K' ≃+* K'')
    (x : 𝓞 K) :
    RingOfIntegers.mapRingEquiv (e.trans e') x = RingOfIntegers.mapRingEquiv e' (RingOfIntegers.mapRingEquiv e x) :=
  RingOfIntegers.ext rfl

theorem comp_refl_eq {K : Type} [Field K] (σ : K →+* ℂ) : σ.comp (RingEquiv.refl K).toRingHom = σ :=
  RingHom.ext fun _ => rfl

theorem comp_trans_eq {K K' K'' : Type} [Field K] [Field K'] [Field K''] (e : K ≃+* K') (e' : K' ≃+* K'')
    (σ : K'' →+* ℂ) : (σ.comp e'.toRingHom).comp e.toRingHom = σ.comp (e.trans e').toRingHom :=
  RingHom.ext fun _ => rfl

theorem IsCoreIso.trans {T T' T'' : Core D} {h : LawsM T} {h' : LawsM T'} {h'' : LawsM T''} {j : ℕ}
    {fe : T.Q.c.F ≃+* T'.Q.c.F} {Φ : T.R j ≃+* T'.R j}
    {pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)}
    {fe' : T'.Q.c.F ≃+* T''.Q.c.F} {Φ' : T'.R j ≃+* T''.R j}
    {pl' : HeightOneSpectrum (𝓞 T'.Q.c.F) → HeightOneSpectrum (𝓞 T''.Q.c.F)}
    (A : IsCoreIso h h' j fe Φ pl) (B : IsCoreIso h' h'' j fe' Φ' pl') :
    IsCoreIso h h'' j (fe.trans fe') (Φ.trans Φ') (pl' ∘ pl) where
  fe_coe x := (B.fe_coe _).trans (A.fe_coe x)
  smul a f := by
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, A.smul, B.smul]
    rfl
  eO x := by rw [mapRingEquiv_trans_apply, B.eO, A.eO]
  pl_bij := B.pl_bij.comp A.pl_bij
  pl_mem la x := by rw [A.pl_mem, B.pl_mem, mapRingEquiv_trans_apply]; rfl
  pl_norm la := (B.pl_norm (pl la)).trans (A.pl_norm la)
  cusp w f := (A.cusp w f).trans (B.cusp w _)
  vals la v := (A.vals la v).trans (B.vals (pl la) _)
  sup w σ f hf := by
    rw [RingEquiv.trans_apply, B.sup w σ _ ((A.cusp w f).1 hf), A.sup w _ f hf, comp_trans_eq]
  l2 w σ f hf := by
    rw [RingEquiv.trans_apply, B.l2 w σ _ ((A.cusp w f).1 hf), A.l2 w _ f hf, comp_trans_eq]

def IsCoreIso.ptEquiv {T T' : Core D} {h : LawsM T} {h' : LawsM T'} {j : ℕ} {fe : T.Q.c.F ≃+* T'.Q.c.F}
    {Φ : T.R j ≃+* T'.R j} {pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)}
    (A : IsCoreIso h h' j fe Φ pl) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : T.PtM j la ≃ T'.PtM j (pl la) where
  toFun y := ⟨y.1 ∘ Φ.symm, (A.vals la y.1).1 y.2⟩
  invFun z := ⟨z.1 ∘ Φ, (A.vals la _).2 (by
    have e : (z.1 ∘ Φ) ∘ Φ.symm = z.1 := funext fun x => by simp
    rw [e]; exact z.2)⟩
  left_inv y := Subtype.ext (funext fun x => by simp)
  right_inv z := Subtype.ext (funext fun x => by simp)

def CxIndep (D : D7) : Prop :=
  ∀ (T : Core D) (U : ∀ j (σ : T.Q.c.F →+* ℂ), Unf (T.Q.Xo j) T.Q.c σ D.R.r) (V : ℕ → (T.Q.c.F →+* ℂ) → HSp D)
    (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
    (Kf : ∀ j σ, Subgroup (GA D (V j σ))) (h : LawsM T)
    (h' : LawsM { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf }) (j : ℕ), InR D j →
    ∀ w : WeightFamilies.Wt D j, T.C j w = Core.C { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf } j w ∧
      ∀ (σ : T.Q.c.F →+* ℂ), ∀ f ∈ T.C j w,
        T.Ns j w σ f = Core.Ns { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf } j w σ f ∧
        NlM h j w σ f = NlM h' j w σ f

theorem isCoreIso_of_cx (hc : CxIndep D) (T : Core D) (U : ∀ j (σ : T.Q.c.F →+* ℂ), Unf (T.Q.Xo j) T.Q.c σ D.R.r)
    (V : ℕ → (T.Q.c.F →+* ℂ) → HSp D) (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r)
    (mu : ∀ j σ, GA D (V j σ) → ℂ) (Kf : ∀ j σ, Subgroup (GA D (V j σ))) (h : LawsM T)
    (h' : LawsM { T with U := U, V := V, dict := dict, mu := mu, Kf := Kf }) (j : ℕ) (hj : InR D j) :
    IsCoreIso h h' j (RingEquiv.refl _) (RingEquiv.refl _) id where
  fe_coe _ := rfl
  smul _ _ := rfl
  eO x := by rw [mapRingEquiv_refl_apply]
  pl_bij := Function.bijective_id
  pl_mem la x := by rw [mapRingEquiv_refl_apply]; rfl
  pl_norm _ := rfl
  cusp w f := by rw [(hc T U V dict mu Kf h h' j hj w).1]; rfl
  vals _ _ := Iff.rfl
  sup w σ f hf := by rw [comp_refl_eq]; exact ((hc T U V dict mu Kf h h' j hj w).2 σ f hf).1.symm
  l2 w σ f hf := by rw [comp_refl_eq]; exact ((hc T U V dict mu Kf h h' j hj w).2 σ f hf).2.symm

def ParTr (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsCore T) (_h' : LawsCore T') (j : ℕ), InR D j →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsCore { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)),
      IsCoreIso _h.toLawsM h''.toLawsM j fe Φ pl

def INV (D : D7) : Prop :=
  ∀ (T T' : Core D) (h : LawsCore T) (h' : LawsCore T') (j : ℕ), InR D j →
    ∃ (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso h.toLawsM h'.toLawsM j fe Φ pl

theorem inv_of (hp : ParTr D) (hc : CxIndep D) : INV D := by
  intro T T' h h' j hj
  obtain ⟨U, V, dict, mu, Kf, h'', fe, Φ, pl, A⟩ := hp T T' h h' j hj
  exact ⟨_, _, _, A.trans (isCoreIso_of_cx hc { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf } T'.U T'.V T'.dict T'.mu
    T'.Kf h''.toLawsM h'.toLawsM j hj)⟩

def ParTrPb (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsM T) (_h' : LawsM T'), T.pb = T'.pb → ∀ (j : ℕ), InR D j →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsM { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso _h h'' j fe Φ pl

def INVPb (D : D7) : Prop :=
  ∀ (T T' : Core D) (h : LawsM T) (h' : LawsM T'), T.pb = T'.pb → ∀ (j : ℕ), InR D j →
    ∃ (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso h h' j fe Φ pl

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.OneCusp
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open scoped ComplexConjugate

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem not_isIso_of_p0_zero (X : Data E r) (h0 : X.p0 = 0) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, hh, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact ⟨_, h⟩
    · exact ⟨τ, (X.cmType τ).2 h⟩
  obtain ⟨P, hP, hG⟩ := X.signature ⟨τ, hτ⟩
  set v : Fin r → ℂ := fun a => τ (ξ a) with hv
  set w : Fin r → ℂ := P⁻¹.mulVec v with hw
  have hPw : P.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have h1 : hermC τ X.Gm v v = 0 := by
    have := congrArg τ hh
    rw [map_zero] at this
    rw [← this]
    simp only [hermC, herm, map_sum, map_mul, hv, cc, IsCMField.complexEmbedding_complexConj]
  have h2 : hermC τ X.Gm v v = ∑ a, ∑ b, w a * gram τ X.Gm P a b * conj (w b) := by
    have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
        ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := fun f =>
      calc ∑ x, ∑ y, ∑ a, ∑ b, f x y a b = ∑ x, ∑ a, ∑ y, ∑ b, f x y a b :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ y, ∑ b, f x y a b := Finset.sum_comm
        _ = ∑ a, ∑ x, ∑ b, ∑ y, f x y a b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ x, ∑ y, f x y a b := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have L : ∀ x y, P.mulVec w x * τ (X.Gm x y) * conj (P.mulVec w y) =
        ∑ a, ∑ b, w a * (P x a * τ (X.Gm x y) * conj (P y b)) * conj (w b) := by
      intro x y
      simp only [Matrix.mulVec, dotProduct]
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]; ring
    rw [← hPw]
    simp only [hermC, L, gram, col, Matrix.of_apply]
    rw [sw]
    simp only [Finset.mul_sum, Finset.sum_mul]
  have h3 : ∑ a, Complex.normSq (w a) = 0 := by
    rw [h2, hG] at h1
    have : ∑ a, (Complex.normSq (w a) : ℂ) = 0 := by
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib, ← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb.symm]) (by simp)]
      simp [sgn, h0, Complex.mul_conj]
    exact_mod_cast this
  have h4 : w = 0 := funext fun a => Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg _).mp h3 a (Finset.mem_univ a))
  apply hne
  funext a
  have : v a = 0 := by rw [← hPw, h4, Matrix.mulVec_zero]; rfl
  exact (map_eq_zero τ).mp this

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

theorem dom_zero : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩

end

variable {D : D7} {T : Core D}

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RealPt
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

def RealPtSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ] : Prop :=
  ∀ ζ : PtsG G la, ∃ (y : E.Pt' la) (T : CDVR) (ι : Loc ζ →+* T.V) (_ : IsLocalHom ι)
    (hunr : ∃ ϖ : Loc ζ, Irreducible ϖ ∧ Irreducible (ι ϖ)) (ev : Rp (xplus X E hM) la G.N →+* T.Fr)
    (hu : IsUnit (ev (sec (xplus X E hM) la G.w 0))),
    (∀ (w : WeightFamilies.Wt D j) (F : B.Cusp j w), E.vAt' la y (X.inc w F) =
      nval T.V (ep (unifO (xplus X E hM) la G.N) ζ) (ev (emb (xplus X E hM) la G.N (X.inc w F)))) ∧
    ∀ x : ↥(Frac0 (xplus X E hM) la G.w),
      IsLocalization.Away.lift (sec (xplus X E hM) la G.w 0) hu (x : Lw (xplus X E hM) la G.w) =
        phiAt ζ T.Fr ι h (addVal_map_of_unr ι hunr) (toOsK (xplus X E hM) la G.w x)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RecConj
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  (c : Coeff l)

private theorem rt0_conj_ne_lemma : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro h2
  have hre := Complex.conj_eq_iff_re.mp h2
  have hsq := H.sqrt_neg_disc_sq
  rw [← hre] at hsq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h3 : ((H.rt0.re ^ 2 : ℝ) : ℂ) = ((-(H.d : ℝ) : ℝ) : ℂ) := by push_cast; exact hsq
  have h4 := Complex.ofReal_injective h3
  nlinarith [sq_nonneg H.rt0.re]

theorem not_good_conj {σ : c.F →+* ℂ} (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  unfold GoodEmb at h h'
  simp only [RingHom.comp_apply] at h h'
  rw [h] at h'
  exact rt0_conj_ne_lemma h'

private theorem imaginary_root_conj_lemma_2 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
  have h1 : ((starRingEnd ℂ) H.rt0) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exact absurd h rt0_conj_ne_lemma
  · exact h

theorem goodOf_conj (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have key : ∀ τ : c.F →+* ℂ, GoodEmb c τ ∨ GoodEmb c ((starRingEnd ℂ).comp τ) := by
    intro τ
    unfold GoodEmb
    simp only [RingHom.comp_apply]
    generalize hxd : (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ = x
    have hx : (x : ℂ) = H.rt0 := by rw [← hxd]; rfl
    have hx2 : x ^ 2 = -((H.d : ℕ) : c.F) := by
      apply Subtype.ext
      have h0 : (x : ℂ) ^ 2 = -((H.d : ℕ) : ℂ) := by rw [hx, H.sqrt_neg_disc_sq]
      exact_mod_cast h0
    have hsq : (τ x) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, hx2, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl h
    · right
      rw [h, map_neg, imaginary_root_conj_lemma_2, neg_neg]
  unfold goodOf
  by_cases h1 : GoodEmb c σ
  · have h2 := not_good_conj c h1
    rw [if_neg h2, if_pos h1]
    ext x
    simp
  · rcases key σ with h | h
    · exact absurd h h1
    · rw [if_pos h, if_neg h1]

end

variable {D : D7} {T : Core D} (h : LawsCore T)

theorem recB_supN_conj (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (F : (recB h).Cusp j w) :
    (recB h).supN j w ((starRingEnd ℂ).comp σ) F = (recB h).supN j w σ F := by
  simp [recB, mkB, cutN, Core.Ns, goodOf_conj]

end Formalism.L2.Pj
end
end

