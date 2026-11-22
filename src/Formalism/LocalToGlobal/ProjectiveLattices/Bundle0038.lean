import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
section
noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem volPair_of_tie (hT : VolTieG D) (V : HSp D) (hs : V.SigOK) : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  have h := hT V hs
  clear hT
  obtain ⟨⟨μ, hμ⟩, hb⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hb μ hμ
  refine ⟨(μ, 𝓕), ?_⟩
  exact ⟨hμ, h𝓕⟩

theorem quotSupp_of (V : HSp D) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    QuotSupp V := by
  intro φ hφc hφinv hae g0
  by_contra hg0
  haveI : Countable (GQ V) := by
    unfold GQ
    exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have hvp : IsVolPair D V (volPair V).1 (volPair V).2 := by
    have e : volPair V = hP.choose := by
      unfold volPair
      rw [dif_pos hP]
    rw [e]
    exact hP.choose_spec
  haveI : (volPair V).1.IsHaarMeasure := hvp.1.1
  haveI : BorelSpace (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : MeasurableMul (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA _ _
  haveI : MeasurableConstSMul (GQ V) (GA D V) := ⟨fun c => measurable_const_mul (c : GA D V)⟩
  haveI : SMulInvariantMeasure (GQ V) (GA D V) (volPair V).1 :=
    ⟨fun c s _ => measure_preimage_mul (volPair V).1 (c : GA D V) s⟩
  let O : Set (GA D V) := {g | φ g ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun hφc continuous_const
  have hOinv : ∀ γ : GQ V, γ • O = O := by
    intro γ
    ext g
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show φ ((γ : GA D V) * x) ≠ 0
      rw [hφinv _ γ.2]
      exact hx
    · intro hg
      refine ⟨((γ⁻¹ : GQ V) : GA D V) * g, ?_, ?_⟩
      · show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0
        rw [hφinv _ (γ⁻¹).2]
        exact hg
      · show (γ : GA D V) * (((γ⁻¹ : GQ V) : GA D V) * g) = g
        rw [← mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_mul]
  have hpos : 0 < (volPair V).1 O := hO.measure_pos _ ⟨g0, hg0⟩
  have hOF : (volPair V).1 (O ∩ (volPair V).2) ≠ 0 := fun h =>
    hpos.ne' (hvp.2.measure_zero_of_invariant O hOinv h)
  let S : Set (AutQ V) := {q | ¬ onQ V φ q = (0 : AutQ V → ℂ) q}
  have h0 : muQ1 V S = 0 := ae_iff.mp hae
  have hS : muQ V S = 0 := by
    unfold muQ1 at h0
    rw [if_pos (show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ from hV), Measure.smul_apply,
      smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (ENNReal.inv_eq_zero.mp h) hV.2
    · exact h
  have hmeas : AEMeasurable (autMk V) ((volPair V).1.restrict (volPair V).2) := by
    by_contra hnm
    apply hV.1
    unfold muQ
    simp [Measure.map_of_not_aemeasurable hnm]
  have hpre : autMk V ⁻¹' S = O := by
    ext g
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel (GQ V)) g
    rw [QuotientGroup.rightRel_apply] at hrel
    have hv : φ (autMk V g).out = φ g := by
      have e : g = (g * (autMk V g).out⁻¹) * (autMk V g).out := by group
      conv_rhs => rw [e]
      rw [hφinv _ hrel]
    show ¬ φ (autMk V g).out = 0 ↔ φ g ≠ 0
    rw [hv]
  have hle := Measure.le_map_apply hmeas S
  rw [hpre, Measure.restrict_apply hO.measurableSet] at hle
  have e2 : muQ V S = Measure.map (autMk V) ((volPair V).1.restrict (volPair V).2) S := rfl
  rw [← e2, hS] at hle
  exact hOF (le_antisymm hle (zero_le))

section Dom

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem aeDom_of {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2)
    (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) : AeDom U σ V dict mu := by
  intro la P hPm hae k x hx
  have key : ∀ Q ∈ holSub (U σ).X la,
      ((∀ γ ∈ GQ V, ∀ g, adel V dict mu Q (γ * g) = adel V dict mu Q g) ∧
        Continuous (adel V dict mu Q)) ∧
      ∀ k, (∀ x ∈ ((U σ).X k).dom, ∀ b ∈ Bor ((U σ).X k).Ψ r, Q k (rmul x b) = bchar (la k) b * Q k x) ∧
        ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Q k (lact γ x) = ((U σ).X k).χ (la k) γ * Q k x := by
    intro Q hQ
    unfold holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      refine ⟨hA la Q hQ, fun k => ?_⟩
      have hs := (hQ k).1.1
      exact ⟨hs.2.1, hs.2.2⟩
    | zero =>
      refine ⟨⟨fun γ _ g => by simp, by rw [map_zero]; exact continuous_zero⟩,
        fun k => ⟨fun x _ b _ => by simp, fun γ _ x _ => by simp⟩⟩
    | add Q₁ Q₂ _ _ h1 h2 =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_add, Pi.add_apply, Pi.add_apply, h1.1.1 γ hγ g, h2.1.1 γ hγ g]
      · rw [map_add]
        exact h1.1.2.add h2.1.2
      · simp only [Pi.add_apply]
        rw [(h1.2 k).1 x hx b hb, (h2.2 k).1 x hx b hb, mul_add]
      · simp only [Pi.add_apply]
        rw [(h1.2 k).2 γ hγ x hx, (h2.2 k).2 γ hγ x hx, mul_add]
    | smul a Q _ h =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h.1.1 γ hγ g]
      · rw [map_smul]
        exact h.1.2.const_smul a
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).1 x hx b hb]
        ring
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).2 γ hγ x hx]
        ring
  obtain ⟨⟨hinv, hcont⟩, hlaw⟩ := key P hPm
  have hz := quotSupp_of V hV hP (adel V dict mu P) hcont hinv hae
  obtain ⟨-, -, -, hd4, hd5, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hd5 k x hx
  have h0 : P (dict g).1 (dict g).2 = 0 := by
    have e : mu g * P (dict g).1 (dict g).2 = 0 := hz g
    have hmu0 : mu g ≠ 0 := by
      intro h
      have h1 := hmu.2.1 g
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    exact (mul_eq_zero.mp e).resolve_left hmu0
  have hdom := hd4 g
  rw [hg] at h0 hdom
  exact eq_zero_of_orbit _ (la k) (P k) (hlaw k).1 (hlaw k).2 hx hγ hb hdom h0

end Dom

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7}

theorem spanIn_ne_bot {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)]
    [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j))
    (j : ℕ) (w : WeightFamilies.Wt D j) {s : Set (R j)} {f : R j} (hf : f ∈ s) (hc : f ∈ cutR C j w) (h0 : f ≠ 0) :
    spanIn C j w s ≠ ⊥ := by
  intro hb
  apply h0
  have hmem : (⟨f, hc⟩ : cutR C j w) ∈ spanIn C j w s := by
    unfold spanIn
    exact Submodule.subset_span hf
  rw [hb] at hmem
  exact congrArg Subtype.val ((Submodule.mem_bot _).1 hmem)

variable (T : Top D)

namespace Top

abbrev PtA (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  PtV (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) (T.G.PY j (WeightAlgebra.resCh la)) (T.G.lies j la) la

def th (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) := thGen (T.Q.Xo j) T.Q.c (T.nab j) (wtA w) w.n

def sh (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) :=
  shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (wtA w) w.n (T.dδ j w.n)

end Top

variable {T} (h : LawsP T)

def recPJ (j : ℕ) (hj : InR D j) : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  mkX T.Q.eO T.C h.toLawsCore.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.toLawsCore.Nl h.toLawsCore.hNs
    h.toLawsCore.hNl h.toLawsCore.hle T.Cu T.Xc T.Xc_lat T.FJt h.toLawsCore.sg
    T.G.P j hj (h.toLawsCore.mul j hj) (T.G.dat j) (fun hm => (h.datum_condition j hj.1 hm).1) (fun hm => (h.datum_condition j hj.1 hm).2)
    (T.PtA j) (fun _ y => imgV y) (fun _ y => vAtV y) (fun _ y => isVal_vAt y)
    (fun _ f _ => nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) f) (T.th j) (T.sh j)

def recX : WeightAlgebra.Prov D (recB h.toLawsCore) T.G.P := fun j h1 h2 => recPJ h j ⟨h1, h2⟩

theorem recPJ_pt_nonempty (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    Nonempty ((recPJ h j hj).Pt la) := by
  obtain ⟨S, io, e, ho, y, hy⟩ := h.ptNe j hj la
  obtain ⟨η, hη⟩ := T.G.liesTotal h.points_condition h.bc66 hj la S io e ho y hy
  exact ⟨PtV.mk la ho y hy η hη⟩

theorem recPJ_vAt_inc (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la)
    (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w) :
    (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 := by
  dsimp only [recPJ, mkX, vG, incG]
  refine le_antisymm (iInf_le_of_le (deg w) (le_of_eq ?_)) (le_iInf fun m => ?_)
  · change vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff (deg w)) = _
    first
      | simp [AddMonoidAlgebra.coeff_single]
      | simp [AddMonoidAlgebra.single_apply]
      | simp [Finsupp.single_apply]
      | exact (0 : Nat)
  · change _ ≤ vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff m)
    by_cases hm : deg w = m
    · subst hm
      first
        | simp [AddMonoidAlgebra.coeff_single]
        | simp [AddMonoidAlgebra.single_apply]
        | simp [Finsupp.single_apply]
    · first
        | simp [AddMonoidAlgebra.coeff_single, hm]
        | simp [AddMonoidAlgebra.single_apply, hm]
        | simp [Finsupp.single_apply, hm]
      rw [(isVal_vAt y).zero]
      exact le_top

theorem recPJ_thAll_ne_bot (j : ℕ) (hj : InR D j) (hm' : j < D.R.m) (w : WeightFamilies.Wt D j) (hn : 0 < w.n)
    (hr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ w.n) (hD : DF (T.Q.Dw j) (wtA w) + 2 ≤ T.Q.l.M)
    (hl : LastPos (T.Q.Dw j) (wtA w)) (hP : ∃ P ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n, P ≠ 0) :
    (recPJ h j hj).thAll w ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := h.thNe j hj.1 hm' _ _ (dom_wtA w) hn hr hD hP
  have hc : f ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]; exact h.thCusp j hj _ _ (dom_wtA w) hl f hf
  exact spanIn_ne_bot T.C j w hf hc hf0

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Field

variable (c c' : Coeff l) (hle : c.F ≤ c'.F)

abbrev incF : c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def AlgOver (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] : Prop :=
  ∀ a : c.F, algebraMap c'.F S (incF c c' hle a) = algebraMap c.F S a

variable {c c'}

theorem embK_incF (τ : E →+* ℂ) (a : 𝓞 E) : incF c c' hle (embK c τ a) = embK c' τ a :=
  Subtype.ext rfl

theorem sOf_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) :
    sOf c' S = sOf c S := by
  unfold sOf
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact h ((IntermediateField.inclusion c.le).toRingHom x)

variable {Xo : Moduli Dw l}

theorem isEigAt_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (τ : E →+* ℂ) (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsEigAt (Xo := Xo) c' τ v ↔ IsEigAt (Xo := Xo) c τ v := by
  have key : ∀ a : 𝓞 E, algebraMap c'.F S (embK c' τ a) = algebraMap c.F S (embK c τ a) := by
    intro a
    rw [← embK_incF hle τ a]
    exact h (embK c τ a)
  unfold IsEigAt
  simp only [key]

def FrPt.res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c' S) : FrPt Xo c S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h)
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).1 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).2 he)
  s := y.s
  gen := y.gen

def FrPt.ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : FrPt Xo c' S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h).symm
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).2 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).1 he)
  s := y.s
  gen := y.gen

theorem FrPt.res_ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : (y.ext hle h).res hle h = y := rfl

theorem FrPt.ext_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c' S) : (y.res hle h).ext hle h = y := rfl

variable {r : ℕ}

def unfBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  { Comp := (U (σ'.comp (incF c c' hle))).Comp
    fin := (U (σ'.comp (incF c c' hle))).fin
    X := (U (σ'.comp (incF c c' hle))).X
    un := fun k x => FrPt.ext hle (S := CAt σ') (fun _ => rfl) ((U (σ'.comp (incF c c' hle))).un k x) }

def IsBC {m : ℕ} (f' : Rul Xo c') (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
    evR Xo c' f' y = ∑ i, algebraMap c'.F S (as i) * evR Xo c (fs i) (y.res hle h)

def CuspBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f' ∈ cusp Xo c' (unfBC hle U) a n,
    ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ cusp Xo c U a n) ∧ IsBC hle f' as fs

def ActBC {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') :
    Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : G) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) (f' : Rul Xo c'),
    f' ∈ sec Xo c' a n → (∀ i, fs i ∈ sec Xo c a n) →
    IsBC hle f' as fs → IsBC hle (act' g f') as (fun i => act g (fs i))

end Field

section Comparison₂

variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} {r : ℕ}
  {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

def OneMapTieC (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c)
    (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F) (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (cc : (unfBC hle U σ0').Comp → ℂ)
    (ph : ℂ) : Prop :=
  LL ≤ c'.F ∧ CuspBC hle U ∧ ActBC hle act act' ∧
    OneMapRow Xo c' V (unfBC hle U σ0') dict mu xr a act' dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unfBC hle U) a n) cc ph

end Comparison₂

end Gen

section Dict

open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {n r : ℕ}

def MarkBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ}
    {lab : Fin g → D.host.E →+* ℂ} (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (h γ : GA D V) : Prop :=
  γ ∈ GQ V ∧
    ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w

def CXiVal {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop :=
  ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧ ∀ t : Tup, IsUnf (U₂ t) ∧ (∀ k, ModelW V hr ((U₂ t).X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif (dδ t).Xo₂ ((σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)).comp
          (IntermediateField.inclusion (dδ t).c₂.le).toRingHom)
        (fun j => relab (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) (e j).1))
      (ik : (U₂ t).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U₂ t).X k).Λ)
      (th : ∀ k, ((U₂ t).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat (U₂ t) V hr (dict₂ t) ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy (U₂ t) V hr (dict₂ t) ι F ik φ h γ →
        rdU (U₂ t) (dδ t).cδ (dict₂ t h).1 (dict₂ t h).2 =
          c0 * ((xi t (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

variable {c c' : Coeff l} (hle : c.F ≤ c'.F)

def actLev (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (g : G) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) =>
    levActR (Xo := Xo) (c := c) lev g' y y') g

def ActLev (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) : Prop :=
  ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g' y y')

def OneMapTieP (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    (V : HSp D) (hr : V.rank = r) (dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    {Tup : Type} (dδ : Tup → DeltaDat Xo c' n) (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (bad : Tup → ℕ) (Lh : ∀ t, Cl' t → Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (La : ∀ t, Cl' t → GenLat D.host.E n) (Nc : ∀ t, Cl' t → ℕ) (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F)
    (ep : ∀ t, Cl' t → c'.F) (B : Tup → Ideal (𝓞 D.host.E) → c'.F)
    (epF : Tup → Submodule (𝓞 D.host.E) (Fin n → D.host.E) → c'.F) (q1 d cond : ℕ)
    {Ix : Type} [Fintype Ix] (pl : Ix → (D.host.E →+* ℂ)) (lam : Ix → DomWeight n)
    (io : VVc c' lam →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (hw : VVc c' lam)
    (φ : ∀ t, (Fin n → LevQc Dw (dδ t).l₂) → c'.F) (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0'.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (thAd : ∀ t, (Cl' t → VVc c' lam) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → VVc c' lam) → Prop)
    (cc : (unfBC hle U σ0').Comp → ℂ) (ph : ℂ) : Prop :=
  Nonempty Tup ∧ (∀ t, Nonempty (Cl' t)) ∧
    ActLev (Xo := Xo) c lev ∧ ActLev (Xo := Xo) c' lev ∧
    (∀ t, BadPin (bad t) q1 d cond) ∧ RepsCov Xo c' Cl' dδ bad Lh La Nc gam ∧
    (∀ t k, ep t k = epF t (Lh t k)) ∧ (∀ t, EpIs (Dw := Dw) c' (bad t) (B t) (epF t) ∧ BAbs c' (B t)) ∧
    IoLFRec c' (fun τ => embF c' (pl τ)) lam a io hw ∧
    WPin Xo c' Cl' dδ φ w ∧
    CovPin Xo c' dδ ∧
    CXiVal V hr σ0' dδ U₂ dict₂ ι x₀ xi ∧
    OneMapTieC hle LL U σ0' V dict mu xr a (actLev c lev) (actLev c' lev) dδ Cl' w La Nc gam vol ep io thAd Pl cc ph

end Dict

end Formalism.L2.Pj
end
end

