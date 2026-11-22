import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.LowIrr

def zR (P Q R S : ℕ) : Fin R × Fin (P + Q) → Ln P Q R S := fun w => (finSumFinEquiv.symm w.2, .inl w.1)

def yS (P Q R S : ℕ) : Fin S × Fin (P + Q) → Ln P Q R S := fun w => (finSumFinEquiv.symm w.2, .inr w.1)

def kap (P Q k k' : ℕ) : Fin (P + Q) → ℂ := fun i => if (i : ℕ) < P then (k : ℂ) else -(k' : ℂ)

theorem zR_inj (P Q R S : ℕ) : Function.Injective (zR P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [zR, Prod.mk.injEq, Sum.inl.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

theorem yS_inj (P Q R S : ℕ) : Function.Injective (yS P Q R S) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ e
  simp only [yS, Prod.mk.injEq, Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq] at e
  rw [e.1, e.2]

theorem zR_ne_yS (P Q R S : ℕ) (u w) : zR P Q R S u ≠ yS P Q R S w := by
  simp [zR, yS]

theorem zR_or_yS (P Q R S : ℕ) (s : Ln P Q R S) :
    (∃ u, zR P Q R S u = s) ∨ ∃ w, yS P Q R S w = s := by
  obtain ⟨a, c | d⟩ := s
  · exact Or.inl ⟨(c, finSumFinEquiv a), by simp [zR]⟩
  · exact Or.inr ⟨(d, finSumFinEquiv a), by simp [yS]⟩

theorem fockF_rowOp {σ I J : Type} [DecidableEq σ] [Fintype J] (z : I × J → σ) (c d : I)
    (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (GlobalTheory.Capelli.rowOp ℂ z c d f) g = Formalism.REAL.fockF f (GlobalTheory.Capelli.rowOp ℂ z d c g) := by
  rw [GlobalTheory.Capelli.rowOp_apply, GlobalTheory.Capelli.rowOp_apply, Formalism.REAL.fischerInner_sum_left, Formalism.REAL.fischerInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Formalism.REAL.fischerInner_X_mul_left, Formalism.REAL.fischerInner_pderiv_left]

theorem eab_isKC_inl {R S : ℕ} (c d : Fin R) : IsKC (Eab (.inl c) (.inl d) : Mat R S) := by
  intro a b h
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

theorem eab_isKC_inr {R S : ℕ} (c d : Fin S) : IsKC (Eab (.inr c) (.inr d) : Mat R S) := by
  intro a b h
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact absurd trivial h
  · rfl

end GlobalTheory.LowIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section
namespace GlobalTheory.Poinc.Tors.OneOver

theorem exists_frm_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F 1 b) (hw : w.IsGen) (k : ℕ) :
    ∃ wk : Frm D F k b, wk.IsGen ∧ ∀ z J, Good D.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k := by
  obtain ⟨z₀⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' D.P.isLB z₀
  obtain ⟨wk, hwk, hv⟩ := GlobalTheory.TorusExt.exists_gen_val D.P.isLB (DegPre.lineφ D F b) (DegPre.lineε k) hJ₀
    (val w (𝟙 _) z₀ J₀ ^ k)
  refine ⟨wk, hwk, fun z J hJ => ?_⟩
  obtain rfl := CoefBasic.pt_eq z₀ z
  have a₁ := CoefBasic.val_tr hwk (𝟙 _) hJ hJ₀
  have a₂ := CoefBasic.val_tr hw (𝟙 _) hJ hJ₀
  simp only [Category.id_comp] at a₁ a₂
  rw [CoefBasic.prod_line k b (CoefBasic.trU D.P.L z₀ J J₀)] at a₁
  rw [CoefBasic.prod_line 1 b (CoefBasic.trU D.P.L z₀ J J₀)] at a₂
  refine a₁.trans ?_
  rw [hv, a₂]
  simp only [pow_one, mul_pow, inv_pow]

theorem sumF_scale {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hI : AdmBase R I) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} {x : Ix → F} {v v' c : F} (h : SumF I F x v)
    (h' : SumF I F (fun i => c * x i) v') : v' = c * v := by
  have hl := (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix x x v v).2.1 h h (c - 1)
  have e : (fun i => (c - 1) * x i + x i) = fun i => c * x i := funext fun i => by ring
  rw [e, show (c - 1) * v + v = c * v by ring] at hl
  exact (GlobalTheory.AdicSum.sumF_calculus R I hI F Ix (fun i => c * x i) x v' (c * v)).1 h' hl

theorem eq_of_liesOver : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre F) (w w' : Frm D.toPre F 1 g.b) (x x' : TFK (R := R) F ⟶ A.A) (fr : FrAt x) (fr' : FrAt x'), w.IsGen → w'.IsGen → fr.IsGen → fr'.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g w' x' fr' → x = x' := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ w₀ hw₀ g w w' x x' fr fr' hw hw' hfr hfr' H H'
  obtain ⟨wk, hwk, hvk⟩ := exists_frm_pow w hw 4
  obtain ⟨wk', hwk', hvk'⟩ := exists_frm_pow w' hw' 4
  obtain ⟨c, hc, -, hcoef⟩ := ((CoefBasic.coef_basic R D.toPre F 4 g).2.2 wk hwk).2.2.1 wk' hwk'
  have key : ∀ (t : SecA A F 4) (v v' : F), ValAt t x fr v → ValAt t x' fr' v' → v' = c * v := by
    intro t v v' hv hv'
    obtain ⟨s, hs⟩ : ∃ s, U.toUnifPre.ExpandsF F 4 w₀ t s := by
      obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 4) (by norm_num) w₀ hw₀
      exact ⟨e t, (he t _).2 rfl⟩
    have h1 := H 4 (by norm_num) wk hvk hwk t s v hs hv
    have h2 := H' 4 (by norm_num) wk' hvk' hwk' t s v' hs hv'
    rw [show coef s g wk' = fun χ => c * coef s g wk χ from funext (hcoef s)] at h2
    exact sumF_scale hI h1 h2
  obtain ⟨M, s, hcov, haff⟩ := (hL.1.ample _ A 4 le_rfl).2 ⊤ (isAffineOpen_top _)
  choose r hr hsurj using fun i => (haff i).2
  obtain ⟨i', hi⟩ : ∃ i' : A.A.left ⟶ (A.A.hom ⁻¹ᵁ ⊤).toScheme, i' ≫ (A.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨A.A.left.topIso.inv, A.A.left.topIso.inv_hom_id⟩
  have sec : ∀ j, ∃ v : SecA A F 4, ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J),
      Good A.L z J → sA v r z J =
        sval (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd (TFK (R := R) F) A.A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec A.isLB (φ := fun _ : Fin 4 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => 1)
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => ((4 : ℕ) : ℤ))
      (fun U _ f => by
        simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, zpow_natCast])
      (VVRank.pullTo (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (TFK (R := R) F) A.A).left ≫ i') (fun _ => by rw [Category.assoc, hi, Category.comp_id]))
    exact ⟨s', fun Z r z J hJ => (hs' Z r z J hJ).trans (VVRank.sval_pullTo _ _ _ r z hJ)⟩
  choose v hv using sec
  choose a ha using fun j => GlobalTheory.OneBasis.exists_valAt A F hL.1 (v j) x hfr
  choose a' ha' using fun j => GlobalTheory.OneBasis.exists_valAt A F hL.1 (v j) x' hfr'
  have hrel : ∀ j, a' j = c * a j := fun j => key (v j) (a j) (a' j) (ha j) (ha' j)
  have hf : (x.left ≫ i') ≫ (A.A.hom ∣_ ⊤) = (x'.left ≫ i') ≫ (A.A.hom ∣_ ⊤) := by
    rw [← cancel_mono (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens).ι]
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hi, Over.w]
  have e : ∀ y : TFK (R := R) F ⟶ A.A,
      (ptSecT A.A y).left ≫ (snd (TFK (R := R) F) A.A).left ≫ i' = y.left ≫ i' := fun y => by
    rw [← Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
  have key2 : x.left ≫ i' = x'.left ≫ i' := by
    refine AutUniq.hom_eq_of_sval (L := A.L) (φ := fun _ : Fin 4 => (A.A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s
      (A.A.hom ∣_ ⊤) _ _ hf hcov (fun i => (haff i).1) r hr hsurj fun z => ?_
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' A.isLB z
    obtain ⟨κ, hκ⟩ : ∃ κ : F →+* (TFK (R := R) F).left.presheaf.stalk z, ∀ b, cst (R := R) F z b = κ b :=
      ⟨CoefBasic.cstH (R := R) z, CoefBasic.cst_eq z⟩
    refine ⟨J, hJ, Units.map κ.toMonoidHom (Units.mk0 c hc) *
      val (powFrame A.A A.L x' fr' 4) (𝟙 _) z J * (val (powFrame A.A A.L x fr 4) (𝟙 _) z J)⁻¹, fun j => ?_⟩
    have p := (hv j _ (ptSecT A.A x).left z J hJ).symm.trans (ha j z J hJ)
    have q := (hv j _ (ptSecT A.A x').left z J hJ).symm.trans (ha' j z J hJ)
    rw [e] at p q
    rw [p, q, hrel j]
    have hinv := Units.inv_mul (val (powFrame A.A A.L x fr 4) (𝟙 _) z J)
    simp only [Units.val_mul, Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      hκ, map_mul, id] at hinv ⊢
    linear_combination (-(κ c * (val (powFrame A.A A.L x' fr' 4) (𝟙 _) z J).val * κ (a j))) * hinv
  have := congrArg (fun q => q ≫ (A.A.hom ⁻¹ᵁ ⊤).ι) key2
  simp only [Category.assoc, hi, Category.comp_id] at this
  exact Over.OverMorphism.ext this

end GlobalTheory.Poinc.Tors.OneOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.TopForm GlobalTheory.ChartGlue

namespace GlobalTheory

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts p' τ → CxPts p σ}

theorem CxPts.ev_appLE_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ r) {U : Y.Opens} {W : Y'.Opens} (h : W ≤ r ⁻¹ᵁ U)
    (g : Γ(Y, U)) {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ W) :
    ev p' τ W ((r.appLE U W h).hom g) z = ev p σ U g (m z) :=
  (ev_res h hz _).trans (ev_of_comp hm U g z).symm

def CxPts.bcMap (w : r ≫ p = p' ≫ spMap ρ) (τ : k' →+* ℂ) (z : CxPts p' τ) : CxPts p (τ.comp ρ) :=
  ⟨z.1 ≫ r, by
    rw [Category.assoc, w, ← Category.assoc, z.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl⟩

theorem CxPts.bijective_bcMap (H : IsPullback r p' p (spMap ρ)) (τ : k' →+* ℂ) :
    Function.Bijective (bcMap H.w τ) := by
  refine ⟨fun z z' h => Subtype.ext (H.hom_ext (congrArg Subtype.val h) (z.2.trans z'.2.symm)), fun y => ?_⟩
  have e : y.1 ≫ p = spMap τ ≫ spMap ρ := by
    rw [y.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  exact ⟨⟨H.lift y.1 (spMap τ) e, H.lift_snd _ _ _⟩, Subtype.ext (H.lift_fst _ _ _)⟩

theorem etale_coords_baseChange (H : IsPullback r p' p (spMap ρ)) {U : Y.Opens} (hU : IsAffineOpen U)
    {x : Fin D → Γ(Y, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
      fun a => (r.appLE U _ inf_le_left).hom (x a)).Etale := by
  letI := ρ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := k) (S := k') (σ := Fin D)
  have h₁ := (CommRingCat.isPushout_of_isPushout k k' (MvPolynomial (Fin D) k) (MvPolynomial (Fin D) k')).flip
  have h₂ := isPushout_sections p p' r H U hU
  have e₁ : CommRingCat.ofHom (algX p U) = CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k)) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p U) x) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  have e₂ : CommRingCat.ofHom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤)) =
      CommRingCat.ofHom (algebraMap k' (MvPolynomial (Fin D) k')) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
        fun a => (r.appLE U _ inf_le_left).hom (x a)) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  rw [e₁, e₂] at h₂
  have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
  · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
    exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun (appLE_comp_algX H.w (inf_le_left : r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _)) a
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.X a))
    rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem AlgChart.exists_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r)
    (c : AlgChart p σ D) {z : CxPts p' τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart p' τ D, z ∈ c'.e.source ∧ ∃ h : c'.U ≤ r ⁻¹ᵁ c.U,
      ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a) := by
  have hU : IsAffineOpen (r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤) := by
    rw [show r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤ = r ⁻¹ᵁ c.U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H c.affine
  obtain ⟨⟨e, U, hU', x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale hU _
    (etale_coords_baseChange H c.affine c.etale)
    (mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (c.source_subset hz), mem_ptsIn_top⟩ : z ∈ ptsIn p' τ _)
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, inf_le_left, fun _ => rfl⟩

variable [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

theorem AlgChart.rv_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r) (K : CanonLB p D)
    {c : AlgChart p σ D} {c' : AlgChart p' τ D} (h : c'.U ≤ r ⁻¹ᵁ c.U)
    (hx : ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a)) {a : (K.baseChange H).bundle.ι} {z : CxPts p' τ}
    (hz : z ∈ ptsIn p' τ c'.U) (ha : z ∈ ptsIn p' τ ((K.baseChange H).bundle.U a)) :
    rv τ c'.isFrame ((K.baseChange H).isFrame a) z = rv σ c.isFrame (K.isFrame (a PUnit.unit)) (m z) := by
  have hl : (K.baseChange H).bundle.U a ≤ r ⁻¹ᵁ K.bundle.U (a PUnit.unit) := (GlobalTheory.chartPullPull K.bundle r).le a
  have e := c.rv_mul_jacobian K ((mem_ptsIn_preimage hm).1 (ptsIn_mono h hz))
    ((mem_ptsIn_preimage hm).1 (ptsIn_mono hl ha))
  have e' := c'.rv_mul_jacobian (K.baseChange H) hz ha
  have hW : (K.baseChange H).bundle.U a ⊓ c'.U ≤ r ⁻¹ᵁ (K.bundle.U (a PUnit.unit) ⊓ c.U) := inf_le_inf hl h
  have e₂ := K.jacobian_baseChange H a inf_le_left (W := (K.baseChange H).bundle.U a ⊓ c'.U) inf_le_left hW
    fun i => resG Y inf_le_right (c.x i)
  rw [← ev_appLE_of_comp hm hW _ (mem_ptsIn_inf.2 ⟨ha, hz⟩), ← e₂] at e
  simp only [hx, LB.resG_appLE] at e'
  simp only [LB.appLE_resG] at e
  exact left_inv_eq_right_inv e' ((mul_comm _ _).trans e)

variable {B : LB Y} {B' : LB Y'}

theorem AnRead.topInt_baseChange [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts p' τ)]
    (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r) (hb : Function.Bijective m)
    (R : AnRead p σ D) (R' : AnRead p' τ D) (K : CanonLB p D) (b : ChartPull B' B r)
    {φ : Weight p σ B} {φ' : Weight p' τ B'}
    (hφ : ∀ i z, z ∈ ptsIn p' τ (B'.U i) → φ'.φ i z = φ.φ (b.idx i) (m z))
    {f : (tens K.bundle B).ι → CxPts p σ → ℂ} (hf : f ∈ fibSec p σ _)
    {f' : (tens (K.baseChange H).bundle B').ι → CxPts p' τ → ℂ}
    (hf' : ∀ a i z, z ∈ ptsIn p' τ ((K.baseChange H).bundle.U a) → z ∈ ptsIn p' τ (B'.U i) →
      f' (a, i) z = f (a PUnit.unit, b.idx i) (m z)) :
    R'.topInt (K.baseChange H) φ' f' = R.topInt K φ f := by
  have hc := continuous_of_comp hm
  have key (z : CxPts p' τ) : ∃ S, IsOpen S ∧ m z ∈ S ∧ ∀ A, MeasurableSet A → A ⊆ S →
      R'.topMeasure (K.baseChange H) φ' f' (m ⁻¹' A) = R.topMeasure K φ f A := by
    obtain ⟨c, hz⟩ := AlgChart.exists_mem_source (D := D) (m z)
    obtain ⟨c', hz', h, hx⟩ := c.exists_baseChange H hm hz
    have he (w) (h₁ : w ∈ c'.e.source) (h₂ : m w ∈ c.e.source) : c.e (m w) = c'.e w := by
      ext a
      rw [c.apply_eq _ h₂, c'.apply_eq _ h₁, hx, ev_appLE_of_comp hm h _ (c'.source_subset h₁)]
    have ho := isOpen_over c'.e (c.e.open_source.preimage hc)
    refine ⟨_, c.e.isOpen_inter_preimage ho, ⟨hz, ?_⟩, fun A hA hAS => ?_⟩
    · rw [mem_preimage, he z hz' hz]
      exact mem_over c'.e hz' hz
    have hs (w) (hw : m w ∈ A) : w ∈ c'.e.source := by
      obtain ⟨h₁, h₂, h₃⟩ := hAS hw
      have h₄ := c'.e.map_target h₂
      rw [hb.1 (c.e.injOn h₁ h₃ ((he _ h₄ h₃).trans (c'.e.right_inv h₂)).symm)]
      exact h₄
    have hA' : MeasurableSet (m ⁻¹' A) := hc.measurable hA
    have hi : c.e '' A = c'.e '' (m ⁻¹' A) := by
      conv_lhs => rw [← image_preimage_eq A hb.2, image_image]
      exact image_congr fun w hw => he w (hs w hw) (hAS hw).1
    rw [R'.topMeasure_apply _ _ _ c' hA' hs, R.topMeasure_apply _ _ _ c hA (hAS.trans inter_subset_left), hi]
    refine setLIntegral_congr_fun (measurableSet_image c'.e hA' hs) ?_
    rintro _ ⟨w, hw, rfl⟩
    have h₁ := hs w hw
    have h₂ := (hAS hw).1
    have ha := mem_pick (K.baseChange H).isLB w
    have hi := mem_pick φ'.isLB w
    dsimp only
    rw [c'.e.left_inv h₁, ← he w h₁ h₂, c.e.left_inv h₂, c.topDens_eq K φ hf h₂
      ((mem_ptsIn_preimage hm).1 (ptsIn_mono ((GlobalTheory.chartPullPull K.bundle r).le _) ha))
      ((mem_ptsIn_preimage hm).1 (ptsIn_mono (b.le _) hi)), AlgChart.topDens, AlgChart.topCoeff,
      hφ _ _ hi, hf' _ _ _ ha hi, AlgChart.rv_baseChange H hm K h hx (c'.source_subset h₁) ha]
    rfl
  choose S hS hzS hμ using key
  have e : (R'.topMeasure (K.baseChange H) φ' f').map m = R.topMeasure K φ f :=
    ext_of_cover S hS (fun y => by obtain ⟨z, rfl⟩ := hb.2 y; exact ⟨z, hzS z⟩) fun z A hA h =>
      (Measure.map_apply hc.measurable hA).trans (hμ z A hA h)
  rw [topInt, topInt, ← e, Measure.map_apply hc.measurable MeasurableSet.univ, preimage_univ]

omit [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] in

theorem Vanishing.cval_pullChart (hm : ∀ z, (m z).1 = z.1 ≫ r) (b : ChartPull B' B r) (w : r ≫ p = p' ≫ spMap ρ)
    (f : H0 p B ⊤) {i : B'.ι} {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ (B'.U i)) :
    cval τ (pullChart (W := ⊤) b w le_top f) i z = cval σ f (b.idx i) (m z) :=
  ev_appLE_of_comp hm (inf_le_inf le_top (b.le i)) _ (mem_ptsIn_inf.2 ⟨mem_ptsIn_top, hz⟩)

end BaseChange

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem Adelic.HermSys.weight_baseChange (T : Adelic.HermSys F) (hb : T.BasePointFree) (hh : T.Hermitian)
    (hb' : (T.baseChange E).BasePointFree) (hh' : (T.baseChange E).Hermitian) {τ : E →+* ℂ}
    {m : CxPts (T.baseChange E).str τ → CxPts T.str (τ.comp (algebraMap F E))}
    (hm : ∀ z, (m z).1 = z.1 ≫ T.bcFst E) (i : (T.baseChange E).L.ι) {z : CxPts (T.baseChange E).str τ}
    (hz : z ∈ ptsIn _ τ ((T.baseChange E).L.U i)) :
    ((T.baseChange E).weight hb' hh' τ).φ i z =
      (T.weight hb hh (τ.comp (algebraMap F E))).φ (i PUnit.unit) (m z) := by
  rw [Adelic.HermSys.weight_φ, Adelic.HermSys.weight_φ]
  exact congrArg (fun v => Real.log (archSize (T.A (τ.comp (algebraMap F E))) v ^ 2)) (funext fun j =>
    ev_appLE_of_comp hm ((GlobalTheory.chartPullPull T.L (T.bcFst E)).le i) _ hz)

namespace HilbertSamuel

theorem Geo.sqInt_baseChange (G : Geo F) (j : ℕ) (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (f : ι → H0 G.str (G.adj₂ j) ⊤) :
    (G.baseChange E).sqInt j τ (∑ i, c i • cval τ (G.toExt₂ E j (f i))) =
      G.sqInt j (τ.comp (algebraMap F E)) (∑ i, c i • cval (τ.comp (algebraMap F E)) (f i)) := by
  have H := G.isPullback_fst E
  have hm : ∀ z, (bcMap H.w τ z).1 = z.1 ≫ G.fst E := fun _ => rfl
  have : SmoothOfRelativeDimension G.D (G.baseChange E).str := (G.baseChange E).smooth
  refine AnRead.topInt_baseChange H hm (bijective_bcMap H τ) _ _ G.K
    (chartPullTwist (GlobalTheory.chartPullPull G.L₂ _) (GlobalTheory.chartPullPull G.L _) (j + G.D)) (fun i z hz => ?_)
    (assocVal_mem_holSec (R := AnRead.all _ _ G.D)
      (Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (cval_mem_holSec _ _ _))).1 fun a i z ha hi => ?_
  · have h := mem_ptsIn_inf.1 hz
    refine congrArg₂ (· + ·) (G.second.weight_baseChange E _ _ _ _ hm _ h.1)
      ((Weight.zpow_φ _ _ _ _).trans (Eq.trans (congrArg _ ?_) (Weight.zpow_φ _ _ _ _).symm))
    exact G.toHermSys.weight_baseChange E _ _ _ _ hm _ (mem_pow_iff.1 h.2)
  · have h := mem_ptsIn_inf.1 hi
    have hz : z ∈ ptsIn _ τ (((G.baseChange E).adj₂ j).U ((a, i.1), i.2)) :=
      mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨ha, h.1⟩, h.2⟩
    change (∑ l, c l • cval τ (G.toExt₂ E j (f l))) ((a, i.1), i.2) z =
      (∑ l, c l • cval _ (f l)) ((G.chartAdj₂ E j).idx ((a, i.1), i.2)) (bcMap H.w τ z)
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact ((congrFun (Finset.sum_apply _ _ _) z).trans (Finset.sum_apply _ _ _)).trans
      (Finset.sum_congr rfl fun l _ => congrArg (c l • ·) (cval_pullChart hm (G.chartAdj₂ E j) H.w (f l) hz))

theorem Data.IntegralBound.baseChange {X : Data F} {β κ : (F →+* ℂ) → ℝ} (h : X.IntegralBound β κ) :
    (X.baseChange E).IntegralBound (fun τ => β (τ.comp (algebraMap F E))) fun τ => κ (τ.comp (algebraMap F E)) := by
  intro j hj τ m c f
  have := finite_top X.geom.alg.variety.proj (isLB_tw (isLB_tens X.K.isLB X.isLB₂) X.isLB ((j : ℤ) + X.D))
  let b := Module.finBasis F (H0 X.str (X.adj₂ j) ⊤)
  let b' := (X.isExtension_toExt₂ E j).basis b
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → Fin _ → E, f = fun i => ∑ l, a i l • X.toExt₂ E j (b l) :=
    ⟨fun i l => b'.repr (f i) l, funext fun i => (b'.sum_repr (f i)).symm.trans
      (Finset.sum_congr rfl fun l _ => congrArg _ (IsExtension.basis_apply _ _ _))⟩
  have e₁ : (fun i => (X.baseChange E).inclE hj (∑ l, a i l • X.toExt₂ E j (b l))) =
      fun i => ∑ l, a i l • X.toExtV E j (X.inclE hj (b l)) := funext fun i =>
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun l _ =>
      (map_smul _ _ _).trans (congrArg _ (X.toExtV_inclE E hj _).symm))
  have e₂ : ∑ i, c i • cval τ (∑ l, a i l • X.toExt₂ E j (b l)) =
      ∑ l, (∑ i, c i * τ (a i l)) • cval τ (X.toExt₂ E j (b l)) := by
    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  refine (congrArg (csq _ τ c) e₁).trans_le (((csq_comb _ _ _ _ _).trans
    (csq_extend (X.isExtension_extMap E j) _ τ _ _)).trans_le ((h j hj _ _ _ b).trans_eq (congrArg _ ?_)))
  exact congrArg ENNReal.toReal ((congrArg _ e₂).trans (X.sqInt_baseChange E j τ _ b)).symm

end HilbertSamuel

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfDomainsOfDimLtStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  first | (exact @GlobalTheory.hInv_of_domains_of_dim_lt) | (exact GlobalTheory.hInv_of_domains_of_dim_lt) | (intros; apply GlobalTheory.hInv_of_domains_of_dim_lt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame

abbrev Letter (O : Type) [CommRing O] (N : ℕ) (ι : Type) : Type :=
  (ι → GL (Fin N) O) ⊕ (ι × (Fin N → ℕ))

def evalE (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] Module.End O (NablaT O N lam) :=
  FreeAlgebra.lift O (Sum.elim (grp O N lam) fun p => P p.1 p.2)

def evalPol (O : Type) [CommRing O] (N : ℕ) :
    FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O (MvPolynomial (Fin N × Fin N) O) :=
  FreeAlgebra.lift O fun p => Formalism.GradedWeylDivisibility.rowDivL O p.1 p.2 1

end GlobalTheory.CapelliLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjOfIntegralConjGeneratorStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_conj_of_integral_conj_generator : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) := by
  first | (exact @GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj) | (exact GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj) | (intros; apply GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralCoordsScalarTensorInclusionStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C), ∀ᶠ w : AwayP p in Filter.cofinite,
    IntC G w (inC G (w.1.adicCompletion ℚ) c) := by
  first | (exact @GlobalTheory.FinClsLoc.intC_inC_eventually) | (exact GlobalTheory.FinClsLoc.intC_inC_eventually) | (intros; apply GlobalTheory.FinClsLoc.intC_inC_eventually  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralOfIntegralCoordsLocalTensorStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_isIntegral_of_integralCoordsLocalTensor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ w : AwayP p in Filter.cofinite,
    ∀ x : w.1.adicCompletion ℚ ⊗[ℚ] G.C, IntC G w x → (∃ f : Polynomial (w.1.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) := by
  first | (exact @GlobalTheory.FinClsLoc.intC_isIntegral) | (exact GlobalTheory.FinClsLoc.intC_isIntegral) | (intros; apply GlobalTheory.FinClsLoc.intC_isIntegral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleKernelFiniteSubgroupSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_kernel_finite_subgroupScheme : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : LB A.left) (H : Over (Sp K)) (_ : GrpObj H) (j : H ⟶ A), L.IsLB ∧ IsProjBy A.hom ∧ (∃ t : LB.Gen (Theta A L), t.IsGen) ∧ IsMonHom j ∧ IsClosedImmersion j.left ∧ IsFinite H.hom ∧ ∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  first | exact @GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel | exact GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel | (intros; apply GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel <;> assumption)
end

