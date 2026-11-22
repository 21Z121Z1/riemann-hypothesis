import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivOfLam

open GlobalTheory.CechPic

theorem cls_cube_pair {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (x y : T ⟶ A) (h : (cubeLB A ![x, y] L).IsLB) :
    cls _ h = pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
      pull (1 : T ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.ulift.symm.sum_comp]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := mul_one x
  have p₂ : psum A ![x, y] {1} = y := mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (mul_one y)
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, p₀, p₁, p₂, p₃]
  rw [Finset.card_pair (by decide)]
  simp
  abel

theorem pull_eq_zero_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (hf : ∀ y, f y ∈ L.U i) : pull f (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL f)).2 (GlobalTheory.IsoExtend.exists_gen_of_chart hL f i hf)

theorem exists_chart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : X) : ∃ i, z ∈ L.U i := by
  have : z ∈ (⊤ : X.Opens) := trivial
  rw [← hL.cover] at this
  exact TopologicalSpace.Opens.mem_iSup.1 this

theorem kTriv_of_lam_iso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (P : LB (G2 B).left), P.IsLB →
    (∀ (T : Over S) (x : T ⟶ B), (∃ t : (P.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (L : LB B.left), L.IsLB → LBIso (abelian₂ B L) P → KTriv B L := by
  intro S B _ _ _ P hP H L hL hiso R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ B).left fun p => ?_)
  obtain ⟨V, hpV, c₀, hc₀⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨j, hj⟩ := exists_chart hL ((1 : Over.mk t ⟶ B).left p)
  let W : (Spec (CommRingCat.of R)).Opens := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ B).left ⁻¹ᵁ L.U j
  refine ⟨W, ⟨⟨hpV, hi⟩, hj⟩, ?_⟩
  let T₀ : Over S := Over.mk t
  let TW : Over S := Over.mk (W.ι ≫ t)
  let ιW : TW ⟶ T₀ := Over.homMk W.ι rfl
  suffices key : ιW ≫ x = 1 by
    have := congrArg (fun q => q.left) (key.trans (MonObj.comp_one ιW).symm)
    exact this
  refine H TW (ιW ≫ x) ?_
  let c := cls L hL
  have hLam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hTD : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _

  let O : (T₀ ⊗ B).left.Opens := (fst T₀ B).left ⁻¹ᵁ V
  have h₀ : pull O.ι (cls _ hTD) = 0 := (cls_eq_zero_iff (pull_isLB hTD _)).2 ⟨c₀, hc₀⟩
  let N : B ⊗ TW ⟶ T₀ ⊗ B := lift (snd B TW ≫ ιW) (fst B TW)
  have hN : Set.range N.left.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (fst T₀ B).left (N.left z) ∈ V
    have k : N.left ≫ (fst T₀ B).left = (snd B TW).left ≫ W.ι := by rw [← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, k, Scheme.Hom.comp_apply]
    exact ((snd B TW).left z).2.1.1
  have h₁ : pull N.left (cls _ hTD) = 0 := by
    rw [← IsOpenImmersion.lift_fac O.ι N.left hN, pull_comp, h₀, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B]).left c - pull (snd T₀ B).left c := by
    refine (cls_linComb hL _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul, c]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : pull ((snd B TW ≫ ιW ≫ x) * fst B TW).left c = pull (fst B TW).left c := by
    have k₁ : N ≫ lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B] = (snd B TW ≫ ιW ≫ x) * fst B TW := by
      rw [← Category.assoc, comp_lift, ← Category.assoc, lift_fst, lift_snd, Category.assoc]; rfl
    have k₂ : N ≫ snd T₀ B = fst B TW := lift_snd _ _
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₁, k₂] at h₁
    exact sub_eq_zero.1 h₁
  have hcP : cls _ hP = cls _ hLam := ((cls_eq_iff hLam hP).2 hiso).symm
  have hC : cls _ hLam = pull (fst B B * snd B B).left c - pull (fst B B).left c - pull (snd B B).left c +
      pull (1 : G2 B ⟶ B).left c := cls_cube_pair hL (fst B B) (snd B B) hLam
  have e₃ : pull (snd B TW ≫ ιW ≫ x).left c = 0 := by
    rw [Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ x).left i ?_, map_zero]
    intro y
    exact y.2.1.2
  have e₄ : pull (1 : B ⊗ TW ⟶ B).left c = 0 := by
    have k : (1 : B ⊗ TW ⟶ B) = snd B TW ≫ ιW ≫ (1 : T₀ ⟶ B) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [k, Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ (1 : T₀ ⟶ B)).left j ?_, map_zero]
    intro y
    exact y.2.2
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  show pull _ (cls _ hP) = 0
  rw [hcP, hC, map_add, map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left,
    ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_one,
    e₂, e₃, e₄]
  abel

end GlobalTheory.KTrivOfLam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackNeZeroOfEtaleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalTopFormPullback_ne_zero_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 → GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  first | exact @GlobalTheory.EtaleKlt.ratPull_ne_zero | exact GlobalTheory.EtaleKlt.ratPull_ne_zero | (intros; apply GlobalTheory.EtaleKlt.ratPull_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleReducedEq

theorem isRadical_map_of_etale {Q C : Type} [CommRing Q] [CommRing C] [Algebra Q C]
    [Algebra.Etale Q C] (I : Ideal Q) (hI : I.IsRadical) :
    (I.map (algebraMap Q C)).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have : _root_.IsReduced (TensorProduct Q (Q ⧸ I) C) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (Q ⧸ I) _
  have : _root_.IsReduced (TensorProduct Q C (Q ⧸ I)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm Q C (Q ⧸ I)).toRingEquiv (RingEquiv.injective _)
  exact isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).toRingEquiv
    (RingEquiv.injective _)

theorem etale_eval₂Hom_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale) :
    (MvPolynomial.eval₂Hom ψ N).Etale := by
  have : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway g
  letI : Algebra (MvPolynomial ι R) (MvPolynomial ι A) := MvPolynomial.algebraMvPolynomial
  have : Algebra.Etale (MvPolynomial ι R) (MvPolynomial ι A) :=
    Algebra.Etale.of_equiv (Algebra.IsPushout.equiv R (MvPolynomial ι R) A (MvPolynomial ι A))
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  letI : Algebra (MvPolynomial ι R) C :=
    (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).toAlgebra
  have : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι A) C :=
    IsScalarTower.of_algebraMap_eq fun p => by
      rw [MvPolynomial.algebraMap_def, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
  have : Algebra.Etale (MvPolynomial ι R) C := hE
  exact Algebra.Etale.of_restrictScalars (MvPolynomial ι R) (MvPolynomial ι A) C

theorem isRadical_span_of_away {R A C ι : Type} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] (g δ : R) [IsLocalization.Away g A] (ψ : A →+* C) (N : ι → C)
    (hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap R A)) N).Etale)
    (hδ : (Ideal.span {algebraMap R A δ}).IsRadical) :
    (Ideal.span {ψ (algebraMap R A δ)}).IsRadical := by
  have he := etale_eval₂Hom_of_away g ψ N hE
  letI : Algebra (MvPolynomial ι A) C := (MvPolynomial.eval₂Hom ψ N).toAlgebra
  have : Algebra.Etale (MvPolynomial ι A) C := he
  have hI : (Ideal.map (MvPolynomial.C (σ := ι)) (Ideal.span {algebraMap R A δ})).IsRadical := by
    rw [Ideal.isRadical_iff_quotient_reduced] at hδ ⊢
    exact isReduced_of_injective
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (Ideal.span {algebraMap R A δ})).symm.toRingEquiv
      (RingEquiv.injective _)
  have h2 := isRadical_map_of_etale (C := C) _ hI
  rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, RingHom.algebraMap_toAlgebra,
    RingHom.comp_apply, MvPolynomial.eval₂Hom_C] at h2
  exact h2

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom a = _
  rw [← Functor.map_comp]
  rfl

theorem isUnit_ger_iff_not_mem {X : Scheme.{0}} (Z : Closeds X) (U' : X.affineOpens)
    (δ : Γ(X, U'.1)) (h : (Scheme.IdealSheafData.vanishingIdeal Z).ideal U' = Ideal.span {δ})
    (x : X) (hx : x ∈ U'.1) : IsUnit (ger x hx δ) ↔ x ∉ Z := by
  obtain ⟨P, rfl⟩ : x ∈ Set.range U'.2.fromSpec := by rw [U'.2.range_fromSpec]; exact hx
  have hS : IsClosed (X := PrimeSpectrum Γ(X, U'.1)) (U'.2.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage U'.2.fromSpec.continuous
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at h
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, U'.2.fromSpec_preimage_basicOpen]
  change δ ∉ P.asIdeal ↔ _
  rw [not_iff_not]
  have e := congrArg (P ∈ ·)
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (U'.2.fromSpec ⁻¹' (Z : Set X)))
  rw [hS.closure_eq, h, PrimeSpectrum.zeroLocus_span] at e
  have e3 : (δ ∈ P.asIdeal) = (P ∈ PrimeSpectrum.zeroLocus {δ}) :=
    propext ((PrimeSpectrum.mem_zeroLocus (P : PrimeSpectrum Γ(X, U'.1)) {δ}).trans
      Set.singleton_subset_iff).symm
  exact (e3.trans e).to_iff

theorem mem_iff_not_isUnit_ger {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W)
    (P : Spec Γ(Y, W)) (hP : hW.fromSpec P ∈ W) (c : Γ(Y, W)) :
    c ∈ P.asIdeal ↔ ¬ IsUnit (ger (hW.fromSpec P) hP c) := by
  rw [← Scheme.mem_basicOpen, ← Scheme.Hom.mem_preimage, hW.fromSpec_preimage_basicOpen]
  change _ ↔ ¬ ¬ c ∈ P.asIdeal
  rw [not_not]

theorem reducedEq_pullback_etale : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  intro X Y _ q ι _ Vo U U' hU' W hW hWU N hEt δ hδ
  have part1 : ∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 →
      (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo) := by
    intro z hz hzU'
    rw [ger_appLE q hWU z hz δ, isUnit_map_iff, ← ger_resG hU' (q z) hzU' δ,
      isUnit_ger_iff_not_mem _ U' _ hδ]
    exact not_not
  refine ⟨part1, ?_⟩
  intro W' hW' hW'U' f hf z hz
  obtain ⟨g, hgU', hzg⟩ := U.2.exists_basicOpen_le (V := U'.1) ⟨q z, hW'U' hz⟩ (hWU (hW' hz))
  set g' := resG X hU' g
  set V := X.basicOpen g'
  have hV' : V = X.basicOpen g := by
    simp only [V, g', resG, Scheme.basicOpen_res]
    exact inf_eq_right.2 hgU'
  have hVU' : V ≤ U'.1 := X.basicOpen_le g'
  have hVU : V ≤ U.1 := hVU'.trans hU'
  letI : Algebra Γ(X, U.1) Γ(X, V) := (resG X hVU).toAlgebra
  haveI : IsLocalization.Away g Γ(X, V) := U.2.isLocalization_of_eq_basicOpen g (homOfLE hVU) hV'
  have hδV : (Ideal.span {algebraMap Γ(X, U.1) Γ(X, V) δ}).IsRadical := by
    have e := (Scheme.IdealSheafData.vanishingIdeal Vo.compl).map_ideal_basicOpen U' g'
    rw [hδ, Ideal.map_span, Set.image_singleton] at e
    have hrad : ((Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal
        (X.affineBasicOpen g')).IsRadical := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    rw [← e] at hrad
    have e2 : algebraMap Γ(X, U.1) Γ(X, V) δ =
        (X.presheaf.map (homOfLE (X.basicOpen_le g')).op).hom (resG X hU' δ) :=
      (resG_resG hU' hVU' δ).symm
    rw [e2]
    exact hrad
  have hzV : q z ∈ V := hV' ▸ hzg
  obtain ⟨h, hhle, hzh⟩ := hW.exists_basicOpen_le (V := W' ⊓ q ⁻¹ᵁ V) ⟨z, hz, hzV⟩ (hW' hz)
  set W1 := Y.basicOpen h
  have hW1W : W1 ≤ W := Y.basicOpen_le h
  have hW1V : W1 ≤ q ⁻¹ᵁ V := hhle.trans inf_le_right
  have hW1W' : W1 ≤ W' := hhle.trans inf_le_left
  have hW1 : IsAffineOpen W1 := hW.basicOpen h
  let ψ : Γ(X, V) →+* Γ(Y, W1) := (q.appLE V W1 hW1V).hom
  have hcomp : MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i)) =
      (resG Y hW1W).comp (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.algebraMap_toAlgebra, ψ, resG]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
        Scheme.Hom.appLE_map]
    · intro i
      simp
  have hE : (MvPolynomial.eval₂Hom (ψ.comp (algebraMap Γ(X, U.1) Γ(X, V)))
      (fun i => resG Y hW1W (N i))).Etale := by
    rw [hcomp]
    have h2 : (resG Y hW1W).Etale := by
      letI : Algebra Γ(Y, W) Γ(Y, W1) := (resG Y hW1W).toAlgebra
      haveI : IsLocalization.Away h Γ(Y, W1) := hW.isLocalization_basicOpen h
      exact Algebra.Etale.of_isLocalizationAway h
    exact RingHom.Etale.stableUnderComposition _ _ hEt h2
  have rad := isRadical_span_of_away g δ ψ (fun i => resG Y hW1W (N i)) hE hδV
  have hd : ψ (algebraMap Γ(X, U.1) Γ(X, V) δ) = resG Y hW1W ((q.appLE U.1 W hWU).hom δ) := by
    have := congrArg (fun F => F (MvPolynomial.C δ)) hcomp
    simpa using this
  set d := ψ (algebraMap Γ(X, U.1) Γ(X, V) δ)
  set b := resG Y hW1W' f
  have hb : b ∈ (Ideal.span {d}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hdP, hP⟩
    let P' : Spec Γ(Y, W1) := ⟨P, hP⟩
    have hz' : hW1.fromSpec P' ∈ W1 := by
      rw [← SetLike.mem_coe, ← hW1.range_fromSpec]; exact Set.mem_range_self _
    have hdP' : d ∈ P'.asIdeal := hdP (Ideal.mem_span_singleton_self d)
    rw [mem_iff_not_isUnit_ger hW1 P' hz', hd, ger_resG] at hdP'
    have hq : q (hW1.fromSpec P') ∉ Vo := by
      rw [← part1 _ (hW1W hz') (hVU' (hW1V hz'))]
      exact hdP'
    have hm := hf _ (hW1W' hz') hq
    change b ∈ P'.asIdeal
    rw [mem_iff_not_isUnit_ger hW1 P' hz', ger_resG]
    exact (IsLocalRing.mem_maximalIdeal _).1 hm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (rad hb)
  refine ⟨ger z hzh c, ?_⟩
  rw [← ger_resG hW1W' z hzh f, ← ger_resG hW1W z hzh, ← hd]
  change ger z hzh b = _
  rw [← hc, map_mul, mul_comm]

end GlobalTheory.EtaleReducedEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFiniteTypeIntFiniteIndexProdNormalDomains
section
open scoped nonZeroDivisors

namespace GlobalTheory.ReducedNormalisation

theorem exists_mem_others_not_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Ideal R) (hp : ∀ i, (p i).IsPrime) (hmin : ∀ i j, p i ≤ p j → i = j) (i : ι) :
    ∃ a : R, a ∉ p i ∧ ∀ j, j ≠ i → a ∈ p j := by
  by_contra h
  push_neg at h
  have hle : (Finset.univ.erase i).inf p ≤ p i := by
    intro a ha
    by_contra hai
    obtain ⟨j, hj, hja⟩ := h a hai
    exact hja ((Finset.inf_le (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩) : _ ≤ p j) ha)
  obtain ⟨j, hj, hji⟩ := ((hp i).inf_le').1 hle
  exact (Finset.mem_erase.1 hj).1 (hmin j i hji)

theorem exists_conductor_elem {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] (J : Ideal R)
    (e : R) (he : e ∈ J) (hep : e ∉ p)
    [Module.Finite (R ⧸ p) (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))] :
    ∃ c : R, c ∉ p ∧ c ∈ J ∧ ∀ d : integralClosure (R ⧸ p) (FractionRing (R ⧸ p)),
      ∃ y ∈ J, algebraMap R (FractionRing (R ⧸ p)) y =
        algebraMap R (FractionRing (R ⧸ p)) c * (d : FractionRing (R ⧸ p)) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R ⧸ p)
    (M := integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (R ⧸ p)⁰
    (S := FractionRing (R ⧸ p)) (s.image Subtype.val)
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (b : R ⧸ p)
  have htp : t ∉ p := by
    intro h
    have h0 : (b : R ⧸ p) = 0 := by rw [← ht]; exact Ideal.Quotient.eq_zero_iff_mem.2 h
    exact nonZeroDivisors.coe_ne_zero b h0
  refine ⟨e * t, fun h => (hp.mem_or_mem h).elim hep htp, J.mul_mem_right t he, fun d => ?_⟩
  have key : ∀ d ∈ Submodule.span (R ⧸ p)
      (s : Set (integralClosure (R ⧸ p) (FractionRing (R ⧸ p)))),
      ∃ y ∈ J, algebraMap R (FractionRing (R ⧸ p)) y =
        algebraMap R (FractionRing (R ⧸ p)) (e * t) * (d : FractionRing (R ⧸ p)) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨x, hx⟩ := hb (g : FractionRing (R ⧸ p)) (Finset.mem_image_of_mem Subtype.val hg)
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨e * x', J.mul_mem_right x' he, ?_⟩
      have h1 : algebraMap R (FractionRing (R ⧸ p)) x' =
          algebraMap R (FractionRing (R ⧸ p)) t * (g : FractionRing (R ⧸ p)) := by
        rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) x',
          IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)) t,
          Ideal.Quotient.algebraMap_eq, hx, ht]
        exact Algebra.smul_def _ _
      rw [map_mul, map_mul, h1, mul_assoc]
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨y1, hy1, e1⟩ := hx
      obtain ⟨y2, hy2, e2⟩ := hy
      exact ⟨y1 + y2, J.add_mem hy1 hy2, by
        rw [map_add, e1, e2, ← mul_add]; rfl⟩
    | smul q x _ hx =>
      obtain ⟨y1, hy1, e1⟩ := hx
      obtain ⟨q', rfl⟩ := Ideal.Quotient.mk_surjective q
      refine ⟨q' * y1, J.mul_mem_left q' hy1, ?_⟩
      rw [map_mul, e1]
      show _ = _ * ((Ideal.Quotient.mk p q') • (x : FractionRing (R ⧸ p)))
      rw [Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      ring
  exact key d (by rw [hs]; trivial)

theorem algebraMap_eq_zero_of_mem {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] {z : R}
    (hz : z ∈ p) : algebraMap R (FractionRing (R ⧸ p)) z = 0 := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (FractionRing (R ⧸ p)),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hz, map_zero]

theorem exists_conductor {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Ideal R) [hp : ∀ i, (p i).IsPrime] (hmin : ∀ i j, p i ≤ p j → i = j)
    [∀ i, Module.Finite (R ⧸ p i) (integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i)))] :
    ∃ a : R, (∀ i, a ∉ p i) ∧
      ∀ r : (∀ i, integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i))),
        ∃ y : R, algebraMap R _ y = algebraMap R _ a * r := by
  classical
  have hc : ∀ i, ∃ c : R, c ∉ p i ∧ c ∈ (⨅ (j : ι) (_ : j ≠ i), p j) ∧
      ∀ d : integralClosure (R ⧸ p i) (FractionRing (R ⧸ p i)),
        ∃ y ∈ (⨅ (j : ι) (_ : j ≠ i), p j), algebraMap R (FractionRing (R ⧸ p i)) y =
          algebraMap R (FractionRing (R ⧸ p i)) c * (d : FractionRing (R ⧸ p i)) := by
    intro i
    obtain ⟨e, hei, hej⟩ := exists_mem_others_not_mem p hp hmin i
    exact exists_conductor_elem (p i) _ e
      ((Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).2 fun hj => hej j hj) hei
  choose c hcp hcJ hcd using hc
  have hmemJ : ∀ {i k : ι} {z : R}, z ∈ (⨅ (j : ι) (_ : j ≠ i), p j) → i ≠ k → z ∈ p k :=
    fun hz hik => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz _) (Ne.symm hik)
  refine ⟨∑ i, c i, fun i h => hcp i ?_, fun r => ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h
    refine (Submodule.add_mem_iff_left _ (Submodule.sum_mem _ fun j hj => ?_)).1 h
    exact hmemJ (hcJ j) (Finset.mem_erase.1 hj).1
  choose y hyJ hy using fun i => hcd i (r i)
  refine ⟨∑ i, y i, funext fun k => Subtype.ext ?_⟩
  change algebraMap R (FractionRing (R ⧸ p k)) (∑ i, y i) =
    algebraMap R (FractionRing (R ⧸ p k)) (∑ i, c i) * (r k : FractionRing (R ⧸ p k))
  rw [map_sum, map_sum, Finset.sum_mul, Finset.sum_eq_single k, Finset.sum_eq_single k, hy k]
  · intro i _ hik
    rw [algebraMap_eq_zero_of_mem (p k) (hmemJ (hcJ i) hik), zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h
  · intro i _ hik
    exact algebraMap_eq_zero_of_mem (p k) (hmemJ (hyJ i) hik)
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.ReducedNormalisation

namespace GlobalTheory.ReducedNormalisation

theorem exists_finiteIndex_prod_normalDomains :
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R],
      ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)),
        (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧
        Function.Injective (algebraMap R (∀ i, D i)) ∧
        ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R,
          algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r := by
  intro R _ _ _ _
  classical
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  letI : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let e := Fintype.equivFin (minimalPrimes R)
  let p : Fin (Fintype.card (minimalPrimes R)) → Ideal R := fun k => (e.symm k).1
  haveI hp : ∀ k, (p k).IsPrime := fun k => Ideal.minimalPrimes_isPrime (e.symm k).2
  have hmin : ∀ k l, p k ≤ p l → k = l := by
    intro k l h
    have h2 : p l ≤ p k := (e.symm l).2.2 ⟨hp k, bot_le⟩ h
    exact e.symm.injective (Subtype.ext (le_antisymm h h2))
  haveI : ∀ k, Module.Finite (R ⧸ p k) (integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k))) :=
    fun k => by
      have h : Algebra.EssFiniteType ℤ (R ⧸ p k) := Algebra.instEssFiniteTypeQuotientIdeal ℤ R (p k)
      refine @GlobalTheory.finite_integralClosure_of_essFiniteType_int (R ⧸ p k) _ _ ?_
      convert h
      first | exact Subsingleton.elim _ _ | exact Algebra.algebra_ext _ _ fun r => (eq_intCast _ r).trans (eq_intCast _ r).symm
  obtain ⟨a, ha, hr⟩ := exists_conductor p hmin
  have hzero : ∀ {x : R} (k), algebraMap R (integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k))) x = 0 →
      x ∈ p k := by
    intro x k hx
    have h1 : algebraMap R (FractionRing (R ⧸ p k)) x = 0 := congrArg Subtype.val hx
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p k) (FractionRing (R ⧸ p k)),
      Ideal.Quotient.algebraMap_eq] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1
      ((map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ p k) (FractionRing (R ⧸ p k)))).1 h1)
  refine ⟨Fintype.card (minimalPrimes R),
    fun k => integralClosure (R ⧸ p k) (FractionRing (R ⧸ p k)), fun k => inferInstance,
    fun k => inferInstance, fun k => ⟨inferInstance,
      integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (R ⧸ p k)),
      Module.Finite.trans (R ⧸ p k) _⟩, ?_, a, ?_, hr⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hmem : x ∈ sInf (minimalPrimes R) := Submodule.mem_sInf.2 fun q hq => by
      have := hzero (e ⟨q, hq⟩) (congrFun hx (e ⟨q, hq⟩))
      simpa [p] using this
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    exact IsReduced.eq_zero x (mem_nilradical.mp hmem)
  · intro h0
    obtain ⟨q⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
    apply ha (e q)
    rw [h0]
    exact zero_mem _

end GlobalTheory.ReducedNormalisation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

example : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] [Nontrivial R], ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, Algebra R (D i)), (∀ i, IsDomain (D i) ∧ IsIntegrallyClosed (D i) ∧ Module.Finite R (D i)) ∧ Function.Injective (algebraMap R (∀ i, D i)) ∧ ∃ a : R, a ≠ 0 ∧ ∀ r : (∀ i, D i), ∃ y : R, algebraMap R (∀ i, D i) y = algebraMap R (∀ i, D i) a * r :=
  GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimUniqueOfIsoGrp
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_unique_of_iso_grp : ∀ (S : Scheme.{0}), Nonempty S → ∀ (X Y : Over S) [GrpObj X] (f : X ⟶ Y), IsIso f → ∀ g g' : ℕ, SmoothOfRelativeDimension g X.hom → SmoothOfRelativeDimension g' Y.hom → g = g' := by
  intro S hS X Y _ f hf g g' hg hg'
  obtain ⟨s⟩ := hS
  have : IsIso f.left := (Over.forget S).map_isIso f
  have sq : CommSq f.left X.hom Y.hom (𝟙 S) := ⟨by rw [Over.w f, Category.comp_id]⟩
  have h2 : SmoothOfRelativeDimension g' X.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback (IsPullback.of_horiz_isIso sq) hg'
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique X.hom hg h2 ((η[X]).left s)

end GlobalTheory
end
end

