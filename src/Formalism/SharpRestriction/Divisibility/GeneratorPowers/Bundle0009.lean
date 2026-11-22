import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogClosed
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTieAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ChartPrimTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (wPT : PrimTyG I.G),
    IsPrimG I.G wPT →
    letI := io.toAlgebra
    ∃ wP : PrimTy H Xo, IsPrim wP ∧
      ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
        (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
          LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
        ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
          LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.DescentPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Gen

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

section Jet

variable {k : Type} [CommRing k] {n : ℕ}

def AgreeTo (N : ℕ) (g g' : PS k n d) : Prop :=
  ∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ N → MvPowerSeries.coeff e g = MvPowerSeries.coeff e g'

end Jet

section Lin

variable {k : Type} [CommRing k] {n : ℕ}

def DofNL (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) : PS k n d →ₗ[k] PS k n d where
  toFun := DofN F b u
  map_add' := by
    intro x y
    simp only [DofN, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [DofN, Derivation.map_smul, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

theorem DpolyN_sub {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ e ∈ S, MvPowerSeries.C (P.coeff e) * DmonN F cp u e g := by
  unfold DpolyN
  refine Finset.sum_subset hS (fun e _ he => ?_)
  have h0 : P.coeff e = 0 := by simpa using he
  rw [h0, map_zero, zero_mul]

theorem DpolyN_addP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P Q : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [DpolyN_sub F cp u (P + Q) g (P.support ∪ Q.support) MvPolynomial.support_add,
    DpolyN_sub F cp u P g (P.support ∪ Q.support) Finset.subset_union_left,
    DpolyN_sub F cp u Q g (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_add, map_add, add_mul]

theorem DpolyN_smulP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (c : k) (P : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (c • P) g = c • DpolyN F cp u P g := by
  rw [DpolyN_sub F cp u (c • P) g P.support MvPolynomial.support_smul,
    DpolyN_sub F cp u P g P.support subset_rfl, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, mul_assoc, ← MvPowerSeries.smul_eq_C_mul]

end Lin

theorem nabValN_addP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (P Q : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (P + Q) = nabValN B k h w0 m f cp u P + nabValN B k h w0 m f cp u Q := by
  unfold nabValN
  rw [DpolyN_addP, map_add]

theorem nabValN_smulP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (c : k) (P : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (c • P) = c * nabValN B k h w0 m f cp u P := by
  unfold nabValN
  rw [DpolyN_smulP, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_C]

end Gen

section Asm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

end Asm

section Main

open ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.Pj.SaturatedCharts (toT prodPts_of_combAt combAt_of_prodPts chartTan_of tanAt_of isTan_iff' fst_comp_jetTan)

attribute [local instance] Over.cartesianMonoidalCategory

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem isChartG_reindex (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (tg : κ → (Sp (DualNumber S) ⟶ t.G.left))
    (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (h : IsChartG t x0 d F act tg uvec x) (e : κ' ≃ κ) :
    IsChartG t x0 d F act (fun ℓ => tg (e ℓ)) (fun ℓ => uvec (e ℓ)) x where
  zero := h.zero
  trunc := h.trunc
  law := h.law
  act := h.act
  tan := fun ℓ => h.tan (e ℓ)
  basis := fun v => by
    obtain ⟨b, hb, hbu⟩ := h.basis v
    refine ⟨fun ℓ => b (e ℓ), fun j => ?_, fun a ha => ?_⟩
    · rw [← hb j]
      exact Equiv.sum_comp e (fun ℓ => b ℓ * uvec ℓ j)
    · have h1 : (fun ℓ => a (e.symm ℓ)) = b := hbu _ fun j => by
        rw [← ha j, ← Equiv.sum_comp e (fun ℓ => a (e.symm ℓ) * uvec ℓ j)]
        simp only [Equiv.symm_apply_apply]
      funext ℓ
      rw [← h1]
      simp only [Equiv.symm_apply_apply]

variable {V : Type} [CommRing V] (t : SAB H (Sp V))

theorem combAt_iff {n : ℕ} {x} (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart t.G n x) {m : ℕ}
    (f : Fin m → (Sp (DualNumber V) ⟶ t.G.left)) (hf : ∀ i, f i ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (hft : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t (f i) (hf i))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    IsCombAtG t (𝟙 (Sp V)) f a w ↔ ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw),
      ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ h = ∑ i, a i • ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ (hft i) := by
  constructor
  · intro hc
    have e := prodPts_of_combAt (t := t) f hf a w hw hc
    obtain ⟨h, hh⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    have hT : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw) := by rw [e]; exact h
    exact ⟨hT, (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx e hT h).trans hh⟩
  · rintro ⟨h, hh⟩
    apply combAt_of_prodPts (t := t) f hf a w hw
    obtain ⟨h', hh'⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    exact ReciprocityTheory.ChartRestriction.G.Chart.tan_ext hx h h' (hh.trans hh'.symm)

theorem dir_tan {d : ℕ} (xc : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (hz : ∀ m, homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ xc m = 1) (j : Fin d)
    (ho : (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫
      xc 1).left ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t _ ho) := by
  apply chartTan_of
  refine ⟨ho.trans (Category.comp_id _).symm, ?_⟩
  have h1 := congrArg CommaMorphism.left (hz 1)
  simp only [Over.comp_left] at h1 ⊢
  have h2 : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫
      (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V)).left =
      (homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V)).left := by
    show spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg (fun φ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V => φ.toRingHom) (fst_comp_jetTan ((0 : Fin 1), j))
  rw [← Category.assoc, h2, h1]
  have hobj : spMap (algebraMap V V) ≫ 𝟙 (Sp V) = 𝟙 (Sp V) := by
    rw [Category.comp_id]
    first
      | (rw [Algebra.algebraMap_self]; exact Spec.map_id _)
      | simp [spMap]
  have h3 : ∀ (f g : Sp V ⟶ Sp V), f = g →
      (1 : Over.mk f ⟶ t.G).left = (1 : Over.mk g ⟶ t.G).left := by
    rintro f g rfl; rfl
  exact h3 _ _ hobj

end Lemmas

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ExpTieAlg

variable {S : Type} [CommRing S]

abbrev fam1 {τ : Type} {d : ℕ} (χ : Fin d → MvPowerSeries τ S) : Fin 1 × Fin d → MvPowerSeries τ S := fun p => χ p.2

theorem has_subst_family_of_const {τ : Type} {d : ℕ} {χ : Fin d → MvPowerSeries τ S} (h : ∀ j, constantCoeff (χ j) = 0) :
    HasSubst (fam1 χ) := hasSubst0 fun p => h p.2

theorem eval_single_eq_subst {n d : ℕ} (χ : Pt S n d) (g : PS S 1 d) : ev (n := n) ![χ] g = subst (fam1 χ) g := by
  unfold ev
  congr 1
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i
  rfl

theorem subst_family_comp {τ : Type} {d : ℕ} {χ : Fin d → MvPowerSeries τ S} {ψ : Pt S 1 d}
    (hχ : ∀ j, constantCoeff (χ j) = 0) (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : PS S 1 d) :
    subst (fam1 χ) (subst (fam1 ψ) g) = subst (fam1 fun j => subst (fam1 χ) (ψ j)) g :=
  subst_comp_subst_apply (has_subst_family_of_const hψ) (has_subst_family_of_const hχ) g

open Formalism.FG.SolveVAux in

theorem coeff_single_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [DecidableEq τ]
    (a : σ → MvPowerSeries τ S) (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ S) (t : τ) :
    coeff (Finsupp.single t 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single t 1) (a s) := by
  classical
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hlow : ∀ s, Low 1 (a s) := fun s => (low_one_iff _).2 (ha s)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun s : σ => Finsupp.single s 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finsupp.prod_single_index (h := fun (s : σ) (e : ℕ) => a s ^ e) (pow_zero _), pow_one, smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single t 1) (e.prod fun s n => a s ^ n) = 0 := by
      rcases Nat.lt_or_ge e.degree 2 with hd | hd
      · rcases Nat.lt_or_ge e.degree 1 with hd1 | hd1
        · have he0 : e = 0 := by
            have : e.degree = 0 := by omega
            exact (Finsupp.degree_eq_zero_iff e).1 this
          rw [he0, Finsupp.prod_zero_index, coeff_one, if_neg]
          exact Finsupp.single_ne_zero.2 one_ne_zero
        · obtain ⟨p, rfl⟩ := degree_eq_one e (by omega)
          exact absurd (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ p))) hne
      · have hl := low_P hlow e
        exact hl _ (by rw [Finsupp.degree_single]; omega)
    rw [hz, smul_zero]

open Formalism.FG.SolveVAux in

theorem eq_linear {N : ℕ} (g : MvPowerSeries (Fin 1 × Fin N) S)
    (h : ∀ n : Fin 1 × Fin N →₀ ℕ, n.degree ≠ 1 → coeff n g = 0) :
    g = ∑ q, C (coeff (Finsupp.single ((0 : Fin 1), q) 1) g) * X ((0 : Fin 1), q) := by
  classical
  ext n
  rw [map_sum]
  by_cases hn : n.degree = 1
  · obtain ⟨⟨i, q⟩, rfl⟩ := degree_eq_one n hn
    fin_cases i
    rw [Finset.sum_eq_single q]
    · simp [coeff_X]
    · intro b _ hb
      rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
      intro e
      apply hb
      have := Finsupp.single_left_injective one_ne_zero e
      simp only [Prod.mk.injEq] at this
      exact this.2.symm
    · simp
  · rw [h n hn]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
    rintro rfl
    exact hn (by simp [Finsupp.degree_single])

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpActPf

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ExpTieAlg ExpActPf
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem expAct_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type}
    [CommRing S] [Algebra ℚ S] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB S d O) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : IsExpOf B.G.F uvec φ) (a : O) (cA : Lt1 Dw → S)
    (hE : ∀ (ℓ : Lt1 Dw) (i : Fin d), ∑ j, dLin (B.A.act a) i j * uvec ℓ j = cA ℓ * uvec ℓ i) (j : Fin d) :
    subst (fam1 φ) (B.A.act a j) =
      subst (fun q : Fin 1 × Fin (dL Dw) => cA ((ltIdx Dw).symm q.2) • (X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S))
        (φ j) := by
  classical
  obtain ⟨ℓ, hℓ0, hℓ1, hℓadd⟩ := LogPf.logSt S d B.G
  obtain ⟨ε, hinv, -⟩ := formal_exp_law S d B.G ℓ hℓ0 hℓ1 hℓadd
  have hφ0 := hφ.const
  have hA0 : ∀ i, constantCoeff (B.A.act a i) = 0 := B.A.const a
  have hF0 : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  set w : Fin (dL Dw) → Fin d → S := fun q i => uvec ((ltIdx Dw).symm q) i with hw
  have hlin : ∀ q i, coeff (Finsupp.single ((0 : Fin 1), q) 1) (φ i) = w q i := by
    intro q i
    have := hφ.lin ((ltIdx Dw).symm q) i
    simpa [w] using this
  have hGF : B.G.add (pt S (n := 2) d 0) (pt S (n := 2) d 1) = B.G.F := by
    funext i
    show ev (n := 2) ![pt S d 0, pt S d 1] (B.G.F i) = B.G.F i
    unfold ev
    have : (fun p : Fin 2 × Fin d => (![pt S d 0, pt S d 1] : Fin 2 → Pt S 2 d) p.1 p.2) = X := by
      funext p; rcases p with ⟨b, i⟩; fin_cases b <;> rfl
    rw [this, subst_self]; rfl

  have hBs : HasSubst (fun r : Fin 1 × Fin (dL Dw) =>
      (X ((0 : Fin 2), r.2) + X ((1 : Fin 2), r.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst0 fun r => by simp
  have hA2 : HasSubst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) :=
    hasSubst0 fun p => constantCoeff_subst_eq_zero (hasSubst_cpy _) (fun r => by simp [cpy]) (hφ0 p.2)
  have hadd : ∀ i, ev (n := 2) ![pt S (dL Dw) 0 + pt S (dL Dw) 1] (subst (fam1 φ) (ℓ i)) =
      ev (n := 2) ![pt S (dL Dw) 0] (subst (fam1 φ) (ℓ i)) + ev (n := 2) ![pt S (dL Dw) 1] (subst (fam1 φ) (ℓ i)) := by
    intro i
    rw [eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst]
    have hl : subst (fam1 B.G.F) (ℓ i) =
        subst (fam1 (pt S (n := 2) d 0)) (ℓ i) + subst (fam1 (pt S (n := 2) d 1)) (ℓ i) := by
      have := congrFun hℓadd i
      simp only [comp1, Pi.add_apply, eval_single_eq_subst, hGF] at this
      exact this
    have e1 : subst (fam1 (pt S (dL Dw) 0 + pt S (dL Dw) 1)) (subst (fam1 φ) (ℓ i)) =
        subst (fun p : Fin 2 × Fin d => subst (cpy (S := S) p.1) (φ p.2)) (subst (fam1 B.G.F) (ℓ i)) := by
      rw [subst_comp_subst_apply (has_subst_family_of_const hφ0) (hasSubst0 fun r => by simp [pt]),
        subst_comp_subst_apply (has_subst_family_of_const hF0) hA2]
      congr 1
      funext p
      exact (hφ.hom p.2).symm
    rw [e1, hl, subst_add hA2, subst_comp_subst_apply (has_subst_family_of_const (fun j => by simp [pt])) hA2,
      subst_comp_subst_apply (has_subst_family_of_const (fun j => by simp [pt])) hA2,
      subst_comp_subst_apply (has_subst_family_of_const hφ0) (hasSubst0 fun r => by simp [pt]),
      subst_comp_subst_apply (has_subst_family_of_const hφ0) (hasSubst0 fun r => by simp [pt])]
    congr 1 <;> congr 1 <;> funext p <;> (simp only [pt, fam1, subst_X hA2]; rfl)

  have hlam : ∀ i, subst (fam1 φ) (ℓ i) = ∑ q, C (w q i) * X ((0 : Fin 1), q) := by
    intro i
    have h1 := addition_linear S (dL Dw) (subst (fam1 φ) (ℓ i)) (hadd i)
    rw [eq_linear _ h1]
    apply Finset.sum_congr rfl
    intro q _
    congr 2
    rw [coeff_single_subst (fam1 φ) (fun p => hφ0 p.2) (ℓ i) ((0 : Fin 1), q), Fintype.sum_prod_type,
      Fin.sum_univ_one]
    have hd : ∀ k, coeff (Finsupp.single ((0 : Fin 1), k) 1) (ℓ i) = (1 : Matrix (Fin d) (Fin d) S) i k := by
      intro k; rw [← hℓ1]; rfl
    simp only [fam1, hlin, hd, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]

  have hε0 : ∀ i, constantCoeff (ε i) = 0 := hinv.1
  have hεℓ : ∀ k, subst (fam1 ℓ) (ε k) = X ((0 : Fin 1), k) := by
    intro k
    have := congrFun hinv.2.2.1 k
    simpa [comp1, eval_single_eq_subst, pt] using this
  have hact := action_linear S d O B ℓ ε hℓ0 hℓ1 hℓadd hinv a
  have hcε : ∀ k, constantCoeff (subst (fam1 ε) (B.A.act a k)) = 0 := fun k => by
    rw [const_subst0 (a := fam1 ε) (fun p => hε0 p.2)]; exact hA0 k
  have hℓA : ∀ i, subst (fam1 (B.A.act a)) (ℓ i) = ∑ k, C (dLin (B.A.act a) i k) * ℓ k := by
    intro i
    have hAk : ∀ k, B.A.act a k = subst (fam1 ℓ) (subst (fam1 ε) (B.A.act a k)) := by
      intro k
      rw [subst_family_comp hℓ0 hε0]
      have h2 : (fam1 fun j => subst (fam1 ℓ) (ε j)) = (X : Fin 1 × Fin d → PS S 1 d) := by
        funext p; rcases p with ⟨i, j⟩; fin_cases i; exact hεℓ j
      rw [h2, subst_self]; rfl
    have hi := hact i
    have hcomp : comp1 (B.A.act a) ε = fun k => subst (fam1 ε) (B.A.act a k) := by
      funext k; exact eval_single_eq_subst _ _
    rw [comp1, eval_single_eq_subst, hcomp] at hi
    calc subst (fam1 (B.A.act a)) (ℓ i)
        = subst (fam1 fun k => subst (fam1 ℓ) (subst (fam1 ε) (B.A.act a k))) (ℓ i) := by
          congr 1; funext p; exact hAk p.2
      _ = subst (fam1 ℓ) (subst (fam1 fun k => subst (fam1 ε) (B.A.act a k)) (ℓ i)) :=
          (subst_family_comp hℓ0 hcε _).symm
      _ = subst (fam1 ℓ) (∑ k, C (dLin (B.A.act a) i k) * X ((0 : Fin 1), k)) := by rw [hi]
      _ = ∑ k, C (dLin (B.A.act a) i k) * ℓ k := by
          rw [subst_sum' (has_subst_family_of_const hℓ0)]
          apply Finset.sum_congr rfl
          intro k _
          rw [subst_mul (has_subst_family_of_const hℓ0), subst_C, subst_X (has_subst_family_of_const hℓ0)]

  set D : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun q => cA ((ltIdx Dw).symm q.2) • (X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) with hDdef
  have hD : HasSubst D := hasSubst0 fun q => by simp [D]
  have hP0 : ∀ k, constantCoeff (subst (fam1 φ) (B.A.act a k)) = 0 := fun k => by
    rw [const_subst0 (a := fam1 φ) (fun p => hφ0 p.2)]; exact hA0 k
  have hQ0 : ∀ k, constantCoeff (subst D (φ k)) = 0 := fun k =>
    constantCoeff_subst_eq_zero hD (fun q => by simp [D]) (hφ0 k)
  have hLP : ∀ i, subst (fam1 fun k => subst (fam1 φ) (B.A.act a k)) (ℓ i) =
      ∑ q, C (cA ((ltIdx Dw).symm q) * w q i) * X ((0 : Fin 1), q) := by
    intro i
    rw [← subst_family_comp hφ0 hA0, hℓA i, subst_sum' (has_subst_family_of_const hφ0)]
    simp_rw [subst_mul (has_subst_family_of_const hφ0), subst_C, hlam, Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    have := hE ((ltIdx Dw).symm q) i
    simpa [w] using this
  have hLQ : ∀ i, subst (fam1 fun k => subst D (φ k)) (ℓ i) =
      ∑ q, C (cA ((ltIdx Dw).symm q) * w q i) * X ((0 : Fin 1), q) := by
    intro i
    rw [show (fam1 fun k => subst D (φ k)) = fun s => subst D (fam1 φ s) from rfl,
      ← subst_comp_subst_apply (has_subst_family_of_const hφ0) hD, hlam i, subst_sum' hD]
    apply Finset.sum_congr rfl
    intro q _
    rw [subst_mul hD, subst_C, subst_X hD]
    simp only [D, smul_eq_C_mul, map_mul]
    ring

  have hX : ∀ (P : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), (∀ k, constantCoeff (P k) = 0) →
      P j = subst (fam1 fun i => subst (fam1 P) (ℓ i)) (ε j) := by
    intro P hP
    rw [← subst_family_comp hP hℓ0, hεℓ j, subst_X (has_subst_family_of_const hP)]
  rw [hX _ hP0, hX _ hQ0]
  congr 1
  funext p
  exact (hLP p.2).trans (hLQ p.2).symm

theorem expActOf_of_eig (hE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S]
    [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin C.d),
    ∑ j, dLin (C.B.A.act a) i j * C.uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i) : ExpActOfSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hφ a j
  exact expAct_core C.B C.uvec φ hφ a (fun ℓ => algebraMap c.F S (embK c ℓ.1 a))
    (fun ℓ i => hE E H Dw l Xo c S y C a ℓ i) j

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

