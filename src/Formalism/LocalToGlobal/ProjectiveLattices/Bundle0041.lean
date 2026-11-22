import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Par.Canon (Q : Par D) : Prop :=
  Q.H = hostOfRecord D ∧ ∀ j (hj : InR D j), ∃ hP hd, HEq (Q.Dw j) (datumOfRecord D j hj hP hd)

private theorem lev_eq_lemma {H : Host D.host.E} (l l' : Level H) (hM : l.M = l'.M) (hMb : l.Mb = l'.Mb)
    (hA : l.A = l'.A) : l = l' := by
  cases l
  cases l'
  simp only at hM hMb hA
  subst hM hMb hA
  rfl

private theorem fld_le_lemma_2 {O : Type} [CommRing O] (e : O →+* ℂ) (F F' : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ F] (eO : 𝓞 F ≃+* O) (eO' : 𝓞 F' ≃+* O) (hF : ∀ x : 𝓞 F, e (eO x) = ((x : F) : ℂ))
    (hF' : ∀ x : 𝓞 F', e (eO' x) = ((x : F') : ℂ)) : F ≤ F' := by
  haveI : NumberField F := ⟨⟩
  intro z hz
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (⟨z, hz⟩ : F)
  have key : ∀ t : 𝓞 F, ((t : F) : ℂ) ∈ F' := fun t => by
    have h1 := hF' (eO'.symm (eO t))
    rw [RingEquiv.apply_symm_apply, hF t] at h1
    rw [h1]
    exact (eO'.symm (eO t) : F').2
  have hz' : z = ((a : F) : ℂ) / ((b : F) : ℂ) := by
    have h2 := congrArg (fun w : F => (w : ℂ)) hab
    simpa using h2.symm
  rw [hz']
  exact F'.div_mem (key a) (key b)

private theorem par_eqs_lemma_3 (Q Q' : Par D) (hH : Q.H = Q'.H) (hM : Q.l.M = Q'.l.M) (hA : Q.l.A = Q'.l.A)
    (hMb : Q.l.Mb = Q'.l.Mb)
    (hF : ∀ x : 𝓞 Q.c.F, D.what₂.embLL (D.what₂.OtoLL (Q.eO x)) = ((x : Q.c.F) : ℂ))
    (hF' : ∀ x : 𝓞 Q'.c.F, D.what₂.embLL (D.what₂.OtoLL (Q'.eO x)) = ((x : Q'.c.F) : ℂ)) :
    Q.H = Q'.H ∧ HEq Q.l Q'.l ∧ HEq Q.c Q'.c ∧ HEq Q.eO Q'.eO := by
  obtain ⟨H, l, c, Dw, Xo, eO⟩ := Q
  obtain ⟨H', l', c', Dw', Xo', eO'⟩ := Q'
  simp only at hH hM hA hMb hF hF' ⊢
  subst hH
  have hl := lev_eq_lemma l l' hM hMb hA
  subst hl
  have hFF : c.F = c'.F := by
    haveI := c.fin
    haveI := c'.fin
    exact le_antisymm (fld_le_lemma_2 (D.what₂.embLL.comp D.what₂.OtoLL) _ _ eO eO' hF hF')
      (fld_le_lemma_2 (D.what₂.embLL.comp D.what₂.OtoLL) _ _ eO' eO hF' hF)
  obtain ⟨F, fin, cj, zm, le⟩ := c
  obtain ⟨F', fin', cj', zm', le'⟩ := c'
  simp only at hFF hF hF'
  subst hFF
  refine ⟨rfl, HEq.rfl, HEq.rfl, heq_of_eq ?_⟩
  have inj : ∀ y y' : D.what₂.O, D.what₂.embLL (D.what₂.OtoLL y) = D.what₂.embLL (D.what₂.OtoLL y') → y = y' := by
    intro y y' hy
    obtain ⟨x, rfl⟩ := eO.surjective y
    obtain ⟨x', rfl⟩ := eO.surjective y'
    rw [hF, hF] at hy
    rw [NumberField.RingOfIntegers.ext (Subtype.ext hy)]
  exact RingEquiv.ext fun x => inj _ _ (by rw [hF, hF'])

theorem canon_eqs {T T' : Core D} (h : LawsM T) (h' : LawsM T') (hc : T.Q.Canon) (hc' : T'.Q.Canon)
    (hb : T.pb = T'.pb) (j : ℕ) (hj : InR D j) :
    T.Q.H = T'.Q.H ∧ HEq T.Q.l T'.Q.l ∧ HEq T.Q.c T'.Q.c ∧ HEq (T.Q.Dw j) (T'.Q.Dw j) ∧
      HEq T.Q.eO T'.Q.eO := by
  have hp := h.pins
  have hp' := h'.pins
  unfold Par.Pins Par.PinLevel Par.PinField at hp hp'
  unfold Par.Canon at hc hc'
  have hH : T.Q.H = T'.Q.H := hc.1.trans hc'.1.symm
  have hMb : T.Q.l.Mb = T'.Q.l.Mb := by rw [h.half.2, h'.half.2, hb]
  obtain ⟨r1, r2, r3, r4⟩ := par_eqs_lemma_3 T.Q T'.Q hH (hp.2.1.1.trans hp'.2.1.1.symm)
    (hp.2.1.2.trans hp'.2.1.2.symm) hMb hp.2.2.1 hp'.2.2.1
  refine ⟨r1, r2, r3, ?_, r4⟩
  obtain ⟨_, _, e1⟩ := hc.2 j hj
  obtain ⟨_, _, e2⟩ := hc'.2 j hj
  exact e1.trans e2.symm

def ModTr (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsM T) (_h' : LawsM T') (j : ℕ), InR D j →
    T.Q.H = T'.Q.H → HEq T.Q.l T'.Q.l → HEq T.Q.c T'.Q.c → HEq (T.Q.Dw j) (T'.Q.Dw j) →
    HEq T.Q.eO T'.Q.eO →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsM { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso _h h'' j fe Φ pl

def ParTrC (D : D7) : Prop :=
  ∀ (T T' : Core D) (_h : LawsM T) (_h' : LawsM T'), T.Q.Canon → T'.Q.Canon → T.pb = T'.pb →
    ∀ (j : ℕ), InR D j →
    ∃ (U : ∀ j (σ : T'.Q.c.F →+* ℂ), Unf (T'.Q.Xo j) T'.Q.c σ D.R.r) (V : ℕ → (T'.Q.c.F →+* ℂ) → HSp D)
      (dict : ∀ j σ, GA D (V j σ) → Σ k, Frame ((U j σ).X k).Ψ D.R.r) (mu : ∀ j σ, GA D (V j σ) → ℂ)
      (Kf : ∀ j σ, Subgroup (GA D (V j σ)))
      (h'' : LawsM { T' with U := U, V := V, dict := dict, mu := mu, Kf := Kf })
      (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso _h h'' j fe Φ pl

def INVC (D : D7) : Prop :=
  ∀ (T T' : Core D) (h : LawsM T) (h' : LawsM T'), T.Q.Canon → T'.Q.Canon → T.pb = T'.pb →
    ∀ (j : ℕ), InR D j →
    ∃ (fe : T.Q.c.F ≃+* T'.Q.c.F) (Φ : T.R j ≃+* T'.R j)
      (pl : HeightOneSpectrum (𝓞 T.Q.c.F) → HeightOneSpectrum (𝓞 T'.Q.c.F)), IsCoreIso h h' j fe Φ pl

theorem parTrC_of (hm : ModTr D) : ParTrC D := by
  intro T T' h h' hc hc' hb j hj
  obtain ⟨e1, e2, e3, e4, e5⟩ := canon_eqs h h' hc hc' hb j hj
  exact hm T T' h h' j hj e1 e2 e3 e4 e5

theorem invC_of (hp : ParTrC D) (hc : CxIndep D) : INVC D := by
  intro T T' h h' hcT hcT' hb j hj
  obtain ⟨U, V, dict, mu, Kf, h'', fe, Φ, pl, hiso⟩ := hp T T' h h' hcT hcT' hb j hj
  have q := hc
  unfold CxIndep at q
  have r := q T' U V dict mu Kf h' h'' j hj
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hiso
  have hm : ∀ w f, f ∈ T.C j w → Φ f ∈ T'.C j w := fun w f hf => by
    rw [(r w).1]; exact (a7 w f).1 hf
  refine ⟨fe, Φ, pl, a1, a2, a3, a4, a5, a6, ?_, a8, ?_, ?_⟩
  · intro w f; rw [(r w).1]; exact a7 w f
  · intro w σ f hf; rw [((r w).2 σ (Φ f) (hm w f hf)).1]; exact a9 w σ f hf
  · intro w σ f hf; rw [((r w).2 σ (Φ f) (hm w f hf)).2]; exact a10 w σ f hf

theorem invC_of_laws (hm : ModTr D) (hR : RdUIndep D) (hL : L2Independence D) : INVC D :=
  invC_of (parTrC_of hm) (cxIndep_of hR hL)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Test

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem wtC_of (hB : BorChartF Xo c) (hA : AllTest Xo c) (σ : c.F →+* ℂ) : WtC Xo c σ := by
  intro a n _ f hf t y y' hb
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  exact wtField_of_borChart hB a n f hf (CAt σ) t y y' (hA _ y) (hA _ y') hb

theorem testRd_rows {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (hC : FrChartF Xo c)
    (hB : BorChartF Xo c) (hA : AllTest Xo c) (hU : IsUnf (U σ)) (hX : BCEx Xo c σ) : TestRd Xo c U σ :=
  testRd_of (U := U) (σ := σ) (hW := evalWD_fr hC) (hU := hU) (hB := hX) (hC := wtC_of hB hA σ)

end Test

section Inv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem rdInvG_of_triv (U : Unf Xo c σ r) (hU : IsUnf U) (hχ : ∀ k la γ, (U.X k).χ la γ = 1) : RdInvG U := by
  intro a n hdn f hf k γ hγ x hx
  rw [rdU_lact (U := U) (hU := hU) (hdn := hdn) (hf := hf) (k := k) γ hγ x hx, hχ, one_mul]

end Inv

section Cont

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def DictLoc (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) : Prop :=
  ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : Comp) (x : GA D V → Frame (X k).Ψ r), ContinuousOn x N ∧
    ∀ g ∈ N, x g ∈ (X k).dom ∧ ∃ γ ∈ (X k).Γ, dict g = ⟨k, lact γ (x g)⟩

theorem adelCont_of {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} (hχ : ∀ k la γ, (X k).χ la γ = 1) (hL : DictLoc V dict) (hm : Continuous mu) :
    AdelCont V dict mu := by
  intro la P hP
  have h1 : ∀ k, P k ∈ (X k).SS (la k) := hP
  simp only [Data.SS, Set.mem_setOf_eq] at h1
  have hS : ∀ k, (X k).IsSec (la k) (P k) := fun k => (h1 k).1.1
  rw [continuous_iff_continuousAt]
  intro g₀
  obtain ⟨N, hN, k, x, hx, hxN⟩ := hL g₀
  have hmap : Set.MapsTo x N (X k).dom := by
    intro g hg
    exact (hxN g hg).1
  have hcont : ContinuousOn (fun g => mu g * P k (x g)) N :=
    hm.continuousOn.mul ((hS k).1.continuousOn.comp hx hmap)
  have heq : ∀ g ∈ N, adel V dict mu P g = mu g * P k (x g) := by
    intro g hg
    obtain ⟨_, γ, hγ, hd⟩ := hxN g hg
    show mu g * P (dict g).1 (dict g).2 = _
    rw [hd]
    rw [(hS k).2.2 γ hγ (x g) (hxN g hg).1, hχ, one_mul]
  have hev : (fun g => mu g * P k (x g)) =ᶠ[nhds g₀] adel V dict mu P := by
    refine Filter.eventuallyEq_of_mem hN ?_
    intro g hg
    exact (heq g hg).symm
  exact (hcont.continuousAt hN).congr hev

theorem adelAut_of_loc {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} (hχ : ∀ k la γ, (X k).χ la γ = 1) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    (hL : DictLoc V dict) (hmc : Continuous mu) : AdelAut V dict mu :=
  adelAut_of hχ hd hm (adelCont_of hχ hL hmc)

end Cont

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

include h hj in

theorem pt_realise (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (y : PtV (T.Q.Xo j) T.Q.c (algCls _ _) Unit (fun _ _ _ _ => True) la) :
    ∃ y' : T.PtA j la, ∀ f, vAtV y' f = vAtV y f := by
  rcases y with ⟨q, S, io, e, ho, z, hz, η, hη, rfl⟩
  obtain ⟨η', hη'⟩ := T.G.liesTotal h.points_condition h.bc66 hj la S io e ho z hz
  exact ⟨PtV.mk la ho z hz η' hη', fun _ => rfl⟩

theorem regularity_R1_extended_points : RegularityR1 (recPJ h j hj) (extAll h j hj) := by
  intro w F hF la y'
  rw [extAll_vAt_inc]
  refine (h.reg j hj).int (dom_wtA w) (cutR_le T.C j w F.2) ?_ la y'.1 y'.2
  rintro la' _ ⟨y, rfl⟩
  obtain ⟨y', hy'⟩ := pt_realise h j hj la' y
  have := hF la' y'
  rw [recPJ_vAt_inc, hy'] at this
  exact this

theorem ereal_lin (a c : ℝ) (v : EReal) (h0 : 0 ≤ v) (ht : v ≠ ⊤) :
    (((a + c * v.toReal : ℝ)) : EReal) = (a : EReal) + (c : EReal) * v := by
  have hb : v ≠ ⊥ := fun hb => by simp [hb] at h0
  conv_rhs => rw [← EReal.coe_toReal ht hb]
  push_cast
  rfl

theorem regularity_R2_extended_points :
    RegularityR2 (recPJ h j hj) (extAll h j hj)
      (fun {wL} {n} gens => NoCommonZero (T.Q.Xo j) T.Q.c fun i => (gens i).1) := by
  have hv : ∀ la (y : (recPJ h j hj).Pt la) w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 :=
    fun la y w F => recPJ_vAt_inc h j hj la y w F
  have ev : ∀ la (y : (extAll h j hj).Pt' la) w (F : (recB h.toLawsCore).Cusp j w),
      (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) = y.1 F.1 :=
    fun la y w F => extAll_vAt_inc h j hj la y w F
  constructor
  · intro wL wE n gens et nus c hc hNZ hX la y'
    have hR := (h.reg j hj).1.2 ⟨(wtA wL, wL.n), dom_wtA wL⟩ ⟨(wtA wE, wE.n), dom_wtA wE⟩ n
      (fun k => ⟨(gens k).1, cutR_le T.C j wL (gens k).2⟩) ⟨et.1, cutR_le T.C j wE et.2⟩ nus c hc hNZ
      (by
        rintro la' ⟨_, ⟨y, rfl⟩⟩
        obtain ⟨y0, hy0⟩ := pt_realise h j hj la' y
        have hx := hX la' y0
        have eet : (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et) = vAtV y et.1 :=
          (hv la' y0 wE et).trans (hy0 _)
        have egs : (⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k))) =
            ⨅ k, vAtV y (gens k).1 := iInf_congr fun k => (hv la' y0 wL (gens k)).trans (hy0 _)
        have h0 : 0 ≤ vAtV y et.1 := le_of_le_of_eq hx.1 eet
        show 0 ≤ vAtV y et.1 ∧ (vAtV y et.1 ≠ ⊤ →
          (⨅ k, vAtV y (gens k).1) ≤ (nus la' : EReal) + (c : EReal) * vAtV y et.1)
        refine ⟨h0, fun hne => ?_⟩
        have hne' : (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et) ≠ ⊤ := by rw [eet]; exact hne
        calc (⨅ k, vAtV y (gens k).1)
            = ⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k)) := egs.symm
          _ ≤ (((nus la' : ℝ) + c * ((recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et)).toReal : ℝ) :
                EReal) := hx.2 hne'
          _ = (nus la' : EReal) + (c : EReal) * vAtV y et.1 := by
              rw [eet]; exact ereal_lin _ _ _ h0 hne)
    obtain ⟨h1, h2⟩ := hR.1 la ⟨y'.1, y'.2⟩
    have eet : (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wE et) = y'.1 et.1 := ev la y' wE et
    have egs : (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k))) =
        ⨅ k, y'.1 (gens k).1 := iInf_congr fun k => ev la y' wL (gens k)
    have h1' : 0 ≤ y'.1 et.1 := h1
    refine ⟨le_of_le_of_eq h1' eet.symm, fun hne => ?_⟩
    have hne' : y'.1 et.1 ≠ ⊤ := by rw [← eet]; exact hne
    calc (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k)))
        = ⨅ k, y'.1 (gens k).1 := egs
      _ ≤ (nus la : EReal) + (c : EReal) * y'.1 et.1 := h2 hne'
      _ = (((nus la : ℝ) + c * ((extAll h j hj).vAt' la y' ((recPJ h j hj).inc wE et)).toReal : ℝ) :
            EReal) := by rw [eet]; exact (ereal_lin _ _ _ h1' hne').symm
  · intro wL n gens nus hNZ hX la y'
    have hR := (h.reg j hj).2 (wtA wL) wL.n (dom_wtA wL) n (fun k => (gens k).1)
      (fun k => cutR_le T.C j wL (gens k).2) hNZ nus
      (by
        rintro la' _ ⟨y, rfl⟩
        obtain ⟨y0, hy0⟩ := pt_realise h j hj la' y
        have egs : (⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k))) =
            ⨅ k, vAtV y (gens k).1 := iInf_congr fun k => (hv la' y0 wL (gens k)).trans (hy0 _)
        exact le_of_eq_of_le egs.symm (hX la' y0)) la y'.1 y'.2
    calc (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k)))
        = ⨅ k, y'.1 (gens k).1 := iInf_congr fun k => ev la y' wL (gens k)
      _ ≤ _ := hR

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.UnifLeaves
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem domStab_holds {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} {F : FamilyUnif Xo σ' ty}
    (M : ModelsOf F r) : ∀ k, ∀ x ∈ (M.X k).dom, (∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom) ∧
      ∀ γ ∈ (M.X k).Γ, lact γ x ∈ (M.X k).dom :=
  fun k _ hx => ⟨fun _ hb => dom_rmul _ hx hb, fun _ hγ => dom_lact _ hx ((M.X k).Γ_stab _ hγ)⟩

def CoverTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (M.X k).dom, ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    F.u k Pm = y.x ∧
    ∀ v : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
      (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
      ∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
        IsCombAt y.x (v τ) cf (y.u τ i)

theorem coverU_of_coverTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : ∀ k x, FrameOK e F M k x (un k x))
    (hT : CoverTri e F M) : CoverU (unfOf e F M un) := by
  intro y
  obtain ⟨k, x, Pm, hPm, hxy, hv⟩ := hT y
  obtain ⟨Pm', hPm', -, hx', hd', -⟩ := hun k x
  have hP : Pm' = Pm := by
    ext a j
    rw [hPm', hPm]
  subst hP
  refine ⟨k, x, ?_⟩
  have hxx : y.x = (un k x).x := hxy.symm.trans hx'.symm
  refine frBor_of_tri (un k x) y hxx fun τ i => ?_
  obtain ⟨cf, h1, h2, h3⟩ := hv (un k x).u hd' τ i
  exact ⟨cf, h1, h2, by rw [← hxx]; exact h3⟩

def FibTri {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ∀ k k' (x : (M.X k).dom) (x' : (M.X k').dom) (Pm : (F.Di k).La →+ (Fin g → ℂ))
    (Pm' : (F.Di k').La →+ (Fin g → ℂ))
    (v v' : ∀ τ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)),
    (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    (∀ a j, Pm' a j = perFr (M.X k') x'.1 (M.φ k' a : Fin r → E) (relab c σ (e j).1) (e j).2) →
    F.u k Pm = F.u k' Pm' →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (v τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k' Pm' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      (v' τ i)) →
    (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → CAt σ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧
      IsCombAt (F.u k Pm) (v τ) cf (v' τ i)) →
    ∃ γ ∈ (M.X k).Γ, ∃ b ∈ Bor (M.X k).Ψ r, (⟨k', x'.1⟩ : Σ k, Frame (M.X k).Ψ r) = ⟨k, rmul (lact γ x.1) b⟩

theorem fibreU_of {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (hun : FramesOK e F M un)
    (hT : TanLin Xo) (hB : FibTri e F M) : FibreU (unfOf e F M un) := by
  intro k k' x x'
  constructor
  · rintro ⟨t, hx, hu, -⟩
    obtain ⟨Pm, hPm, -, hxP, hd, -⟩ := hun.1 k x
    obtain ⟨Pm', hPm', -, hxP', hd', -⟩ := hun.1 k' x'
    refine hB k k' x x' Pm Pm' (un k x).u (un k' x').u hPm hPm' (hxP.symm.trans (hx.symm.trans hxP')) hd hd'
      fun τ i => ?_
    obtain ⟨cf, hcf, htri, hcomb⟩ := hu τ i
    refine ⟨cf, by rw [hcf]; exact Units.isUnit _, htri, ?_⟩
    have e1 : (unfOf e F M un).un k x = un k x := rfl
    rw [e1, hxP] at hcomb
    exact hcomb
  · rintro ⟨γ, hγ, b, hb, heq⟩
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 heq
    have h3 : x'.1 = rmul (lact γ x.1) b := eq_of_heq h2
    have hxg : lact γ x.1 ∈ (M.X k').dom := (domStab_holds M k' x.1 x.2).2 γ hγ
    obtain ⟨t1, ht1, -⟩ := hun.2.2.1 k' γ hγ x hxg
    have hxb : rmul (⟨lact γ x.1, hxg⟩ : (M.X k').dom).1 b ∈ (M.X k').dom := by
      have hx2 := x'.2
      rw [h3] at hx2
      exact hx2
    obtain ⟨t2, ht2, -⟩ := hun.2.1 k' ⟨lact γ x.1, hxg⟩ b hb hxb
    have hx' : (⟨rmul (lact γ x.1) b, hxb⟩ : (M.X k').dom) = x' := Subtype.ext h3.symm
    rw [hx'] at ht2
    exact frBor_trans hT ht1 ht2

end Fam

section Genus

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def ClassOcc (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) : Prop :=
  ∀ h : GA D V, ∃ k, ∃ γ ∈ GQ V,
      ((U.X k).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ k (F.t (ik k) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w)

end Genus

section Rows

variable {D : D7}

theorem coverU_J {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} {hM : ModelEx hN Q hpq j hj σ hσ hR}
    (hF : FrameEx hM) (hT : CoverTri (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM)) :
    CoverU (unfJ hF) :=
  coverU_of_coverTri _ _ _ hF.choose hF.choose_spec.1 hT

theorem fibreU_J {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {j : ℕ} {hj : InR D j}
    {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {hR : RelabType Q.c σ (Q.Dw j)} {hM : ModelEx hN Q hpq j hj σ hσ hR}
    (hF : FrameEx hM) (hT : TanLin (Q.Xo j)) (hB : FibTri (letE (Q.Dw j)) (famJ hN Q hpq j σ hσ hR) (modelsJ hM)) :
    FibreU (unfJ hF) :=
  fibreU_of _ _ _ hF.choose hF.choose_spec hT hB

end Rows

end Formalism.L2.Pj
end
end

