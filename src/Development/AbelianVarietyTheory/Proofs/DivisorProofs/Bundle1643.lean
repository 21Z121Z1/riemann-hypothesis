import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma unit_pullback_left_comp_fst_eq_spMap_comp_unit {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ ≫ η[G].left := by
  simp [Functor.grpObjObj, Functor.monObjObj]
  have h := pullback.condition (f := 𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)
  simp only [Category.comp_id] at h
  erw [pullback.lift_fst]
  rw [← Category.assoc, ← h]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma unit_pullback_left_comp_snd_eq_id {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = 𝟙 _ := by
  have h := Over.w (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G])
  simpa using h

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.semilinear_symm_fixes_unit : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G ≅ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K' ⟶ pullback G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ x := by
  intro K W K' _ _ _ _ _ A _ G _ e he σ x hx₁ hx₂

  have hxη : x = (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left := by
    apply pullback.hom_ext
    · rw [hx₁, unit_pullback_left_comp_fst_eq_spMap_comp_unit]
    · rw [hx₂, unit_pullback_left_comp_snd_eq_id]
      rfl
  have hη : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left ≫ e.hom.left =
      (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') := by
    rw [_root_.GlobalTheory.spMap_comp_spMap]
    congr 1
    ext y
    exact σ.commutes y
  have hinv : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have hmap : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left ≫
      pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _)
        (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [unit_pullback_left_comp_fst_eq_spMap_comp_unit, ← Category.assoc, hσ]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, unit_pullback_left_comp_snd_eq_id]
      simp
  rw [hxη, ← Category.assoc, hη, ← Category.assoc, hmap, Category.assoc, ← hη, Category.assoc,
    hinv, Category.comp_id]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionCompatibility
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.VBExt (AdaptedChart)
open scoped ComplexOrder

namespace GlobalTheory.MetStage

theorem gram_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {E : X.Modules} {r : ℕ} (h : Met p σ E r) (c : Chart E r) {y : CxPts p σ}
    (hc : y ∈ ptsIn p σ c.U) {ι : Type} (φ : ι → Fin r) :
    h.gram (fun a => c.e (φ a)) y = (h.G c y).submatrix φ φ := by
  ext a b; exact h.form_frame c hc _ _

theorem metStages : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → ∀ hl : IsSubbundle l, (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).restrict hl hL = Met.quot (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL ∧ Met.quot (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ = Met.quot (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ := by
  intro k _ X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m w₃ hS₃ n hA hM hL hQ hV hg h hfg hsq hm hl
  have key : ∀ y : CxPts p σ, ∃ (U : X.Opens) (e : Fin n → Γ(A, U)) (t : Fin 1 → Γ(M, U))
      (t₁ : Fin 1 → Γ(B, U)), y ∈ ptsIn p σ U ∧ IsFrame e ∧ IsFrame (fun k => q₀.app U (t k)) ∧
        IsFrame (fun k => q₁.app U (t₁ k)) := by
    intro y
    obtain ⟨a, ha⟩ := Met.exists_adapted hS₀ hA hL y
    obtain ⟨b, hb⟩ := Met.exists_adapted hS₁ hM hQ y
    refine ⟨a.U ⊓ b.U, fun i => resM A inf_le_left (a.e i), fun i => resM M inf_le_left (a.t i),
      fun i => resM B inf_le_right (b.t i), mem_ptsIn_inf.2 ⟨ha, hb⟩, a.he.res inf_le_left, ?_, ?_⟩
    · simp only [app_resM]; exact a.ht.res inf_le_left
    · simp only [app_resM]; exact b.ht.res inf_le_right
  have QS := GlobalTheory.QuotStage.quotStages
  refine ⟨Met.ext_of_exists fun y => ?_, Met.ext_of_exists fun y => ?_⟩
  all_goals
    obtain ⟨U, e, t, t₁, hy, he, ht, ht₁⟩ := key y
    have hgf : ∀ i, g.app U (f.app U (e i)) = u.app U (e i) := fun i => congr(($(hfg)).app U (e i))
    have hsq' : ∀ x : Γ(M, U), l.app U (q₀.app U x) = q₂.app U (g.app U x) :=
      fun x => congr(($(hsq)).app U x)
    have hm' : ∀ x : Γ(B, U), m.app U (q₂.app U x) = q₁.app U x := fun x => congr(($(hm)).app U x)
    let a₀ : AdaptedChart (ShortComplex.mk f q₀ w₀) n 1 := ⟨U, e, t, he, ht⟩
    let a₃ : AdaptedChart (ShortComplex.mk l m w₃) 1 1 := ⟨U, fun i => q₀.app U (t i),
      fun i => q₂.app U (t₁ i), ht, by
        show IsFrame fun k => m.app U (q₂.app U (t₁ k))
        simp only [hm']; exact ht₁⟩
    let t₂ : Fin (1 + 1) → Γ(B, U) := Sum.elim (fun i => g.app U (t i)) t₁ ∘ finSumFinEquiv.symm
    have ht₂ : (fun k => q₂.app U (t₂ k)) = a₃.frame ∘ finSumFinEquiv.symm := by
      funext j
      show q₂.app U (Sum.elim (fun i => g.app U (t i)) t₁ (finSumFinEquiv.symm j)) =
        a₃.frame (finSumFinEquiv.symm j)
      rcases finSumFinEquiv.symm j with i | i
      exacts [(hsq' _).symm, rfl]
    let a₂ : AdaptedChart (ShortComplex.mk u q₂ w₂) n (1 + 1) := ⟨U, e, t₂, he, by
        show IsFrame fun k => q₂.app U (t₂ k)
        rw [ht₂]; exact (a₃.mid hS₃).isFrame⟩
    let T : Fin n ⊕ (Fin 1 ⊕ Fin 1) → Γ(B, U) :=
      Sum.elim (fun i => u.app U (e i)) (Sum.elim (fun i => g.app U (t i)) t₁)
    have h₂T : a₂.frame = T ∘ Sum.map id finSumFinEquiv.symm := by
      funext j; rcases j with i | i <;> rfl
    have hK : (h.gram T y).PosDef := by
      have := (Met.posDef_gram_frame h hS₂ a₂ hy).submatrix
        (Equiv.sumCongr (Equiv.refl (Fin n)) finSumFinEquiv).injective
      rw [h₂T] at this
      convert this using 1
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [Met.gram]
    have hQ₂ : (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).G a₂.quot y =
        (quotGram (h.gram T y)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      rw [Met.quot_G h hS₂ hA hV a₂ hy, h₂T]
      have := (QS (Fin n) (Fin 1 ⊕ Fin 1) (Fin 1)).2 (Fin n) (Fin (1 + 1)) (Equiv.refl _)
        finSumFinEquiv.symm (h.gram T y)
      simp only [Equiv.coe_refl] at this
      exact this
    have h₃ : a₃.frame = fun j => a₂.quot.e (finSumFinEquiv j) := by
      funext j
      exact ((congrFun ht₂ (finSumFinEquiv j)).trans
        (congrArg a₃.frame (finSumFinEquiv.symm_apply_apply j))).symm
    have hG₃ : (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).gram
        a₃.frame y = quotGram (h.gram T y) := by
      rw [h₃]
      refine (gram_chart _ a₂.quot hy finSumFinEquiv).trans ?_
      rw [hQ₂]
      ext i j
      simp only [submatrix_apply, Equiv.symm_apply_apply]
    obtain ⟨e₁, e₂⟩ := (QS (Fin n) (Fin 1) (Fin 1)).1 _ hK
  · refine ⟨a₀.quot, hy, ?_⟩
    have hR : (h.restrict hg hM).gram a₀.frame y =
        (h.gram T y).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := by
      have hT : ∀ i, g.app U (a₀.frame i) = T (Sum.map id Sum.inl i) := by
        rintro (i | i)
        exacts [hgf i, rfl]
      ext i j
      exact (h.form_restrict hg hM _ _ hy).trans (congrArg₂ (h.form · · y) (hT i) (hT j))
    rw [Met.quot_G (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL a₀ hy, hR, ← e₁,
      ← hG₃]
    rfl
  · let a₁ : AdaptedChart (ShortComplex.mk g q₁ w₁) (n + 1) 1 :=
      ⟨U, (a₀.mid hS₀).e, t₁, (a₀.mid hS₀).isFrame, ht₁⟩
    have hc : a₃.quot = a₁.quot := by
      have : (fun i => m.app U (q₂.app U (t₁ i))) = fun i => q₁.app U (t₁ i) :=
        funext fun i => hm' _
      exact (Chart.mk.injEq ..).mpr ⟨rfl, heq_of_eq this⟩
    have hR : h.gram a₁.frame y = ((h.gram T y).submatrix (Equiv.sumAssoc _ _ _)
        (Equiv.sumAssoc _ _ _)).submatrix (Sum.map finSumFinEquiv.symm id)
        (Sum.map finSumFinEquiv.symm id) := by
      have hT : ∀ i, a₁.frame i = T (Equiv.sumAssoc _ _ _ (Sum.map finSumFinEquiv.symm id i)) := by
        rintro (i | i)
        · show g.app U (a₀.frame (finSumFinEquiv.symm i)) =
            T (Equiv.sumAssoc _ _ _ (Sum.inl (finSumFinEquiv.symm i)))
          rcases finSumFinEquiv.symm i with i | i
          exacts [hgf i, rfl]
        · rfl
      ext i j
      exact congrArg₂ (h.form · · y) (hT i) (hT j)
    refine ⟨a₁.quot, hy, ?_⟩
    rw [Met.quot_G (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ a₁ hy, hR,
      (QS (Fin n ⊕ Fin 1) (Fin 1) (Fin 1)).2, submatrix_id_id, ← e₂, ← hG₃, ← hc]
    exact Met.quot_G (S := ShortComplex.mk l m w₃) _ hS₃ hL hQ a₃ hy

end GlobalTheory.MetStage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionMetricCompat
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.CurveDens

open Matrix
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

set_option maxHeartbeats 2000000 in

theorem bcDens_stage_of_frames {A M B L Q V : X.Modules} {f : A ⟶ M} {g : M ⟶ B} {u : A ⟶ B}
    {q₀ : M ⟶ L} {q₁ : B ⟶ Q} {q₂ : B ⟶ V} {w₀ : f ≫ q₀ = 0} {w₁ : g ≫ q₁ = 0} {w₂ : u ≫ q₂ = 0}
    (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact)
    (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) {l : L ⟶ V} {m : V ⟶ Q} {w₃ : l ≫ m = 0}
    (hS₃ : (ShortComplex.mk l m w₃).ShortExact) {n : ℕ} (hA : IsVB A n) (hM : IsVB M (n + 1))
    (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g)
    {h : Met p σ B (n + 1 + 1)} (hfg : f ≫ g = u) (hlq : q₀ ≫ l = g ≫ q₂) (hmq : q₂ ≫ m = q₁)
    (H : h.IsCInf) (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) {U : X.Opens}
    (hyU : y ∈ ptsIn p σ U) (e : Fin n → Γ(A, U)) (t : Fin 1 → Γ(M, U)) (t₁ : Fin 1 → Γ(B, U))
    (he : IsFrame e) (ht : IsFrame fun i => q₀.app U (t i))
    (ht₁ : IsFrame fun i => q₁.app U (t₁ i)) :
    Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y +
        Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y +
        Met.bcDens (S := ShortComplex.mk l m w₃)
          (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  have hfg' (s : Γ(A, U)) : g.app U (f.app U s) = u.app U s := congr(($hfg).app U s)
  have hlq' (s : Γ(M, U)) : l.app U (q₀.app U s) = q₂.app U (g.app U s) := congr(($hlq).app U s)
  have hmq' (s : Γ(B, U)) : m.app U (q₂.app U s) = q₁.app U s := congr(($hmq).app U s)
  let a₀ : AdaptedChart (ShortComplex.mk f q₀ w₀) n 1 := ⟨U, e, t, he, ht⟩
  let a₁ : AdaptedChart (ShortComplex.mk g q₁ w₁) (n + 1) 1 :=
    ⟨U, (a₀.mid hS₀).e, t₁, (a₀.mid hS₀).isFrame, ht₁⟩
  have ht₃ : IsFrame fun i => m.app U (q₂.app U (t₁ i)) := by simpa only [hmq'] using ht₁
  let a₃ : AdaptedChart (ShortComplex.mk l m w₃) 1 1 :=
    ⟨U, fun i => q₀.app U (t i), fun i => q₂.app U (t₁ i), ht, ht₃⟩
  let t₂ : Fin (1 + 1) → Γ(B, U) :=
    Sum.elim (fun i => g.app U (t i)) t₁ ∘ finSumFinEquiv.symm
  have ht₂e (j : Fin 1 ⊕ Fin 1) : q₂.app U (t₂ (finSumFinEquiv j)) = a₃.frame j := by
    rcases j with j | j
    · simp [t₂, a₃, AdaptedChart.frame, hlq']
    · simp [t₂, a₃, AdaptedChart.frame]
  have ht₂ : IsFrame fun i => q₂.app U (t₂ i) := by
    have e₀ : (fun i => q₂.app U (t₂ i)) = (a₃.mid hS₃).e := by
      funext i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      rw [ht₂e]
      simp [AdaptedChart.mid]
    rw [e₀]
    exact (a₃.mid hS₃).isFrame
  let a₂ : AdaptedChart (ShortComplex.mk u q₂ w₂) n (1 + 1) := ⟨U, e, t₂, he, ht₂⟩
  let T : Fin n ⊕ (Fin 1 ⊕ Fin 1) → Γ(B, U) :=
    Sum.elim (fun i => u.app U (e i)) (Sum.elim (fun i => g.app U (t i)) t₁)
  have hT₀ (x : Fin n ⊕ Fin 1) : g.app U (a₀.frame x) = T (Sum.map id Sum.inl x) := by
    rcases x with i | i
    · simp [a₀, T, AdaptedChart.frame, hfg']
    · simp [a₀, T, AdaptedChart.frame]
  have hT₁ (x : (Fin n ⊕ Fin 1) ⊕ Fin 1) :
      a₁.frame (Sum.map finSumFinEquiv id x) = T (Equiv.sumAssoc _ _ _ x) := by
    rcases x with (i | i) | i
    · simp [a₀, a₁, T, AdaptedChart.frame, AdaptedChart.mid, hfg']
    · simp [a₀, a₁, T, AdaptedChart.frame, AdaptedChart.mid]
    · simp [a₁, T, AdaptedChart.frame]
  have hT₂ (x : Fin n ⊕ (Fin 1 ⊕ Fin 1)) :
      a₂.frame (Sum.map id finSumFinEquiv x) = T x := by
    rcases x with i | i | i
    · simp [a₂, T, AdaptedChart.frame]
    · simp [a₂, t₂, T, AdaptedChart.frame]
    · simp [a₂, t₂, T, AdaptedChart.frame]

  let K : CxPts p σ → Matrix (Fin n ⊕ (Fin 1 ⊕ Fin 1)) (Fin n ⊕ (Fin 1 ⊕ Fin 1)) ℂ := h.gram T
  have g₀ {z : CxPts p σ} (hz : z ∈ ptsIn p σ U) :
      (h.restrict hg hM).gram a₀.frame z =
        (K z).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := by
    ext i j
    refine ((h.form_restrict hg hM _ _ hz).trans ?_)
    rw [hT₀, hT₀]
    rfl
  have g₁ {z : CxPts p σ} : (K z).submatrix (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) =
      (h.gram a₁.frame z).submatrix (Sum.map finSumFinEquiv (Equiv.refl (Fin 1)))
        (Sum.map finSumFinEquiv (Equiv.refl (Fin 1))) := by
    ext i j
    change h.form (T _) (T _) z = h.form (a₁.frame _) (a₁.frame _) z
    exact congrArg₂ (fun s s' => h.form s s' z) (hT₁ i).symm (hT₁ j).symm
  have g₂ {z : CxPts p σ} : K z =
      (h.gram a₂.frame z).submatrix (Sum.map (Equiv.refl (Fin n)) finSumFinEquiv)
        (Sum.map (Equiv.refl (Fin n)) finSumFinEquiv) := by
    ext i j
    change h.form (T _) (T _) z = h.form (a₂.frame _) (a₂.frame _) z
    exact congrArg₂ (fun s s' => h.form s s' z) (hT₂ i).symm (hT₂ j).symm
  have g₃ {z : CxPts p σ} (hz : z ∈ ptsIn p σ U) :
      (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).gram a₃.frame z =
        quotGram (K z) := by
    have e₀ := (QuotStage.quotStages (Fin n) (Fin (1 + 1)) Unit).2 (Fin n) (Fin 1 ⊕ Fin 1)
      (Equiv.refl _) finSumFinEquiv (h.gram a₂.frame z)
    ext i j
    rw [g₂, e₀, submatrix_apply, ← Met.quot_G h hS₂ hA hV a₂ hz,
      ← Met.form_frame _ a₂.quot hz]
    exact congrArg₂ (fun s s' => (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1)
      h hS₂ hA hV).form s s' z) (ht₂e i).symm (ht₂e j).symm
  have hW : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn p σ U :=
    eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds
      (ChartGlue.mem_over c.e hy hyU)) fun _ hv => hv.2
  have d₀ : Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y =
      2 * diagVal (extTrace (fun v => (K (c.e.symm v)).submatrix (Sum.map id Sum.inl)
        (Sum.map id Sum.inl)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₀ hA hL a₀ c (H.restrict hg hM) hy hyU, Met.bcForm,
      extTrace_congr (hW.mono fun v hv => g₀ hv)]
  have d₁ : Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y =
      2 * diagVal (extTrace (fun v => (K (c.e.symm v)).submatrix (Equiv.sumAssoc _ _ _)
        (Equiv.sumAssoc _ _ _)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₁ hM hQ a₁ c H hy hyU, Met.bcForm]
    simp only [g₁]
    rw [extTrace_submatrix_sumMap]
  have d₂ : Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y =
      2 * diagVal (extTrace (fun v => K (c.e.symm v)) (c.e y)) (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₂ hA hV a₂ c H hy hyU, Met.bcForm]
    simp only [g₂]
    rw [extTrace_submatrix_sumMap]
  have d₃ : Met.bcDens (S := ShortComplex.mk l m w₃)
      (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y =
      2 * diagVal (extTrace (fun v => quotGram (K (c.e.symm v))) (c.e y))
        (EuclideanSpace.single 0 1) := by
    rw [Met.bcDens_eq hS₃ hL hQ a₃ c (Met.IsCInf.quot hS₂ hA hV H) hy hyU, Met.bcForm,
      extTrace_congr (hW.mono fun v hv => g₃ hv)]
  have hK : MContDiffAt 1 (fun v => K (c.e.symm v)) (c.e y) :=
    ((H.gram T hyU).mContDiffAt c hy).of_le (by norm_cast)
  have hp : ∀ᶠ v in 𝓝 (c.e y), (K (c.e.symm v)).PosDef := hW.mono fun v hv => by
    rw [g₂]
    exact (Met.posDef_gram_frame (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ a₂ hv).submatrix
      ((Equiv.refl (Fin n)).injective.sumMap finSumFinEquiv.injective)
  have key := congrArg (fun w => (-Complex.I * w).re)
    (extTrace_add_extTrace (ReciprocityTheory.L2DbarEstimates.V 1) (Fin n) (Fin 1) (Fin 1) (fun v => K (c.e.symm v))
      (c.e y) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) hK hp)
  simp only [mul_add, Complex.add_re] at key
  rw [d₀, d₁, d₂, d₃]
  simp only [diagVal]
  linarith

theorem bcDens_add_bcDens_stage : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → h.IsCInf → ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, Met.bcDens (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL c y + Met.bcDens (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ c y = Met.bcDens (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV c y + Met.bcDens (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ c y := by
  intro k _ X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m w₃ hS₃ n hA hM hL hQ hV hg h
    hfg hlq hmq H c y hy
  obtain ⟨b₀, hb₀⟩ := Met.exists_adapted (p := p) (σ := σ) hS₀ hA hL y
  obtain ⟨b₁, hb₁⟩ := Met.exists_adapted hS₁ hM hQ y
  refine bcDens_stage_of_frames hS₀ hS₁ hS₂ hS₃ hA hM hL hQ hV hg hfg hlq hmq H c hy
    (U := b₀.U ⊓ b₁.U) (mem_ptsIn_inf.2 ⟨hb₀, hb₁⟩) (fun i => resM A inf_le_left (b₀.e i))
    (fun i => resM M inf_le_left (b₀.t i)) (fun i => resM B inf_le_right (b₁.t i))
    (b₀.he.res inf_le_left) ?_ ?_
  · simp only [app_resM]
    exact b₀.ht.res inf_le_left
  · simp only [app_resM]
    exact b₁.ht.res inf_le_right

end GlobalTheory.CurveDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → SmoothOfRelativeDimension d f := by
  first | exact @GlobalTheory.LogPair.smooth_of_relSnc | exact GlobalTheory.LogPair.smooth_of_relSnc | (intros; apply GlobalTheory.LogPair.smooth_of_relSnc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfUniversalFirstOrderTaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_universal_firstOrder_tangent : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (d : ℕ), Smooth s → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent | exact GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent | (intros; apply GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFractionFieldIsPullbackOfUnramifiedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_fraction_field_isPullback_of_unramified_alt : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → IsPullback (spMap (algebraMap W K')) (spMap (algebraMap K K')) (spMap (algebraMap R W)) (spMap (algebraMap R K)) := by
  first | exact @GlobalTheory.spec_fraction_field_isPullback_of_unramified | exact GlobalTheory.spec_fraction_field_isPullback_of_unramified | (intros; apply GlobalTheory.spec_fraction_field_isPullback_of_unramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharArchimedeanExpRealLinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAddChar_archimedean_exp_realLinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsStdChar D ψ (-1) → IsInfFam θ →
    ∃ β : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧
      ∀ a, β a = -(∑ ρ, θ ρ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a) ⊗ₜ[D.host.F]
        (1 : D.host.E))).re := by
  first | exact @GlobalTheory.StdCharLin.stdChar_mixed_linear | exact GlobalTheory.StdCharLin.stdChar_mixed_linear | (intros; apply GlobalTheory.StdCharLin.stdChar_mixed_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictNormalCrossingsDescentEtaleCompletionStatement
section
open AlgebraicGeometry IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictNormalCrossings_descent_etale_completion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type) [Field k] (m e : ℕ) (φ : A →+* ChartRing k m e) (D : Ideal A), IsEtaleCompletion φ → D.map φ = Ideal.span {∏ i : Fin m, bdParam k m e i} → (∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap φ = (Ideal.span {bdParam k m e i'}).comap φ → i = i') → ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  first | exact @GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion | exact GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion | (intros; apply GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_level_surjective_of_divisible : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M], (∀ x : M, ∃ y, y ^ l = x) → ∀ (n : ℕ) (x : M), x ^ l ^ n = 1 → ∃ t : Tate l M, t.lev n = x := by
  first | exact @GlobalTheory.Published.tate_lev_surj | exact GlobalTheory.Published.tate_lev_surj | (intros; apply GlobalTheory.Published.tate_lev_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionDeterminantRootStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_action_determinant_root : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) k x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → R.ωP i t (1, k) f = ((R.xi t x : Circle) : ℂ) • R.ωP i A.μ0 (1, k) f := by
  first | exact @GlobalTheory.AdTh.weil_twist_base | exact GlobalTheory.AdTh.weil_twist_base | (intros; apply GlobalTheory.AdTh.weil_twist_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefiniteStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_standard_character_indefinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  first | exact @GlobalTheory.WeilContF.continuous_of_level_real | exact GlobalTheory.WeilContF.continuous_of_level_real | (intros; apply GlobalTheory.WeilContF.continuous_of_level_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensityStatement
section
open GlobalTheory.CxForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_power_hermitian_form_density : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), GlobalTheory.CxForm.dens (((∑ a, ∑ b, H a b • GlobalTheory.CxForm.sym (a, b) : GlobalTheory.CxForm.Ev n) ^ n : GlobalTheory.CxForm.Ev n) : GlobalTheory.CxForm.Alt n) = (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := by
  first | exact @GlobalTheory.CxForm.DensPow.dens_pow | exact GlobalTheory.CxForm.DensPow.dens_pow | (intros; apply GlobalTheory.CxForm.DensPow.dens_pow <;> assumption)
end

