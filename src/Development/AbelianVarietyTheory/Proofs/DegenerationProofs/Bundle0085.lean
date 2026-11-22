import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFunctionFieldOfIsDominant
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_functionField_point (X : Scheme.{0}) [IsIntegral X] :
    ∃ (K : Type) (_ : Field K) (pt : Sp K ⟶ X), (∀ w, pt w = genericPoint X) ∧
      ∀ x : K, ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x := by
  let pt : Sp X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)
  refine ⟨X.functionField, inferInstance, pt, fun w => ?_, fun x => ?_⟩
  · rw [Subsingleton.elim w (IsLocalRing.closedPoint X.functionField)]
    exact Scheme.fromSpecStalk_closedPoint
  · obtain ⟨W, hW, g, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) x
    obtain ⟨V, hV, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hW
    have hle' : V ≤ W := hle
    let φ : Γ(X, V) ⟶ CommRingCat.of X.functionField := X.presheaf.germ V (genericPoint X) hz
    have e : pt = Spec.map φ ≫ hV.fromSpec := (hV.fromSpecStalk_eq_fromSpecStalk hz).symm
    refine ⟨V, (X.presheaf.map (homOfLE hle').op).hom g, ⟨_, hz⟩, ?_⟩
    rw [e, valF_eq_valR, valR_eq _ V (le_preimage_specMap_fromSpec hV φ), valMap_specMap_fromSpec]
    exact X.presheaf.germ_res_apply (homOfLE hle') _ hz g

theorem RatModel.exists_functionField_of_isDominant (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (M : RatModel o Ω) (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ M.Z) [IsDominant q] :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra o Ω') (φ : Ω →ₐ[o] Ω') (pt : Sp Ω' ⟶ X),
      Set.range pt = {genericPoint X} ∧
      (∀ x : Ω', ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧
      pt ≫ q = spMap φ.toRingHom ≫ M.pt := by
  obtain ⟨K, _, pt, hpt, honto⟩ := exists_functionField_point X
  have hq : q (genericPoint X) = genericPoint M.Z := by
    have h := (genericPoint_spec X).image q.continuous
    rw [Set.image_univ, q.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec M.Z)
  have hy : ∀ w, (pt ≫ q) w = genericPoint M.Z := fun w => by
    rw [Scheme.Hom.comp_apply, hpt, hq]
  have hs : ∀ w, (pt ≫ q) w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf (pt ≫ q) _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  letI : Algebra o K := (β.comp (algebraMap o Ω)).toAlgebra
  refine ⟨K, inferInstance, inferInstance, { β with commutes' := fun _ => rfl }, pt, ?_, honto, ?_⟩
  · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hpt (IsLocalRing.closedPoint K)⟩, by
      rintro _ ⟨w, rfl⟩
      exact hpt w⟩
  · obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
    have h1 := top_le_preimage_of_specializes hs hz
    have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
    refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
    exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ZH.MulExtend
open GlobalTheory.TorsFrameInt

variable {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {K K' : Type} [Fintype K] [Fintype K']

theorem exists_move_charts (hL : L.IsLB) (hM : M.IsLB) {f : Y ⟶ H} {ψ : Y ⟶ X} (w : LB.Iso (M.pull f) (L.pull ψ))
    (hw : w.IsGen) (φX : K → (X ⟶ X)) (φY : K → (Y ⟶ Y)) (φH : K → (H ⟶ H)) (ε : K → ℤ)
    (h₁ : ∀ k, φY k ≫ ψ = ψ ≫ φX k) (h₂ : ∀ k, φY k ≫ f = f ≫ φH k)
    (α : LB.Gen (LB.LinComb L φX ε)) (hα : α.IsGen) :
    ∃ a : LB.Gen (LB.LinComb M (fun k => f ≫ φH k) ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → M.ι),
        (∀ k, (r ≫ φY k ≫ ψ) z ∈ L.U (p k)) → (∀ k, (r ≫ φY k ≫ f) z ∈ M.U (q k)) →
        gm (r ≫ ψ) z (LB.wchart L φX p) (α.s p) = (∏ k, gw w (r ≫ φY k) z (p k) (fun _ => q k) ^ ε k) *
          gm r z (LB.wchart M (fun k => f ≫ φH k) q) (a.s q) := by
  obtain ⟨b, hb, H⟩ := H1.exists_gen_move hL (pull_isLB hM f) w ((isGen_iff w).1 hw) φX φY ε ψ h₁ α hα
  have le : ∀ j : K → M.ι, LB.wchart M (fun k => f ≫ φH k) j ≤ LB.wchart (M.pull f) φY (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      have : (f ≫ φH k) y ∈ M.U (j k) := Set.mem_iInter.1 hy k
      rw [← h₂ k] at this; exact this)
  refine ⟨⟨fun j => res (le j) (b.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z p q hp hq => ?_⟩
  · refine (gm_res _ y _ hj _).trans ((gen_trans hb (𝟙 Y) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ y _ hj' _).symm))
    refine (gm_pull_g M f (𝟙 Y ≫ φY k) y _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc, h₂]
  · have m : r z ∈ LB.wchart M (fun k => f ≫ φH k) q := Set.mem_iInter.2 fun k => by
      have := hq k
      rw [h₂ k] at this; exact this
    exact (H Z r z p (fun k _ => q k) hp (fun k => Set.mem_iInter.1 (le _ m) k)).trans
      (congrArg₂ (· * ·) rfl (gm_res _ z _ m _).symm)

theorem corr_of_field [IsReduced Y] [Nonempty K] (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (ψ : Y ⟶ X) (h : ∀ k, φ k = ψ) (h' : ∀ k, φ' k = ψ)
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (H : ∀ (F : Type) [Field F] (r : Sp F ⟶ Y) (z : Sp F) J, Good L z J → val t r z J = val t' r z J) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (GenericExtend.eq_of_valR_eq fun x hx ↦ ⟨Y.residueField x, inferInstance,
    Y.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)
  have ho : ∀ o, (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) o = x :=
    fun o ↦ Scheme.fromSpecResidueField_apply x o
  generalize (Y.fromSpecResidueField x : Sp (Y.residueField x) ⟶ Y) = r at ho
  have z : Sp (Y.residueField x) := IsLocalRing.closedPoint _
  have hz : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := (ho z).symm ▸ hx
  obtain ⟨k₀⟩ := ‹Nonempty K›
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := PUnit) (fun _ => r ≫ ψ) (fun _ => j k₀) (fun _ _ _ => rfl)
    (fun _ => by rw [← h k₀]; exact Set.mem_iInter.1 hz.1 k₀)
  have q := H _ r z J hJ
  rw [val_of t r z J j (fun k => by rw [h]; exact (e PUnit.unit).trans (c₁ _ _ ((h _).trans (h _).symm))),
    val_of t' r z J j' (fun k => by rw [h']; exact (e PUnit.unit).trans (c₃ _ _ ((h _).trans (h' _).symm)))] at q
  refine (toStk z).injective ?_
  exact (toStk_valF r _ z hz _).trans ((congrArg Units.val ((gm_res r z _ hz _).trans
    (q.trans (gm_res r z _ hz _).symm))).trans (toStk_valF r _ z hz _).symm)

theorem core {S U HU B : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] (hS : Geo.Tor.IsNormalScheme S)
    [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU)
    (hs : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (hP : IsPullback jH pU p j)
    (h₁ : eU ≫ jH = j ≫ e) (hL : L.IsLB) (hM : M.IsLB) (eX : B ⟶ X) (u : U ⟶ B) (ψ : HU ⟶ X)
    (h₃ : eU ≫ ψ = u ≫ eX) (nH : H ⟶ H) (nU : HU ⟶ HU) (nX : X ⟶ X)
    (c₁ : nU ≫ ψ = ψ ≫ nX) (c₂ : nU ≫ jH = jH ≫ nH) (c₃ : eU ≫ nU = eU) (c₄ : e ≫ nH = e)
    (w : LB.Iso (M.pull jH) (L.pull ψ)) (hw : w.IsGen)
    (rig : LB.Gen (L.pull eX)) (rigM : LB.Gen (M.pull e)) (hrigM : rigM.IsGen) (N : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, nX] ![N, -1])) (hα : α.IsGen)
    (hn : ∀ (Z : Scheme.{0}) (t : Z ⟶ B) (z : Z) J, Good L z J →
      val α (t ≫ eX) z J = val rig t z J ^ N * (val rig t z J)⁻¹)
    (hr : ∀ (F : Type) [Field F] (x : Sp F ⟶ U) (z : Sp F) J J', Good L z J → Good M z J' →
      val rig (x ≫ u) z J = wv w (x ≫ eU) z J J' * val rigM (x ≫ j) z J') :
    ∃ κ : LB.Gen (LB.LinComb M (K := Fin 2) ![𝟙 H, nH] ![N, -1]), κ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z) (a a' : L.ι) (b b' : M.ι),
        (r ≫ ψ) z ∈ L.U a → ((r ≫ nU) ≫ ψ) z ∈ L.U a' → (r ≫ jH) z ∈ M.U b → ((r ≫ nU) ≫ jH) z ∈ M.U b' →
        gm (r ≫ ψ) z (LB.wchart L ![𝟙 X, nX] ![a, a']) (α.s ![a, a']) * gw w (r ≫ nU) z a' (fun _ => b') =
          gw w r z a (fun _ => b) ^ N * gm (r ≫ jH) z (LB.wchart M ![𝟙 H, nH] ![b, b']) (κ.s ![b, b']) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have d₁ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ ψ = ψ ≫ ![𝟙 X, nX] k := fun k => by
    fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₁]
  have d₂ : ∀ k : Fin 2, ![𝟙 _, nU] k ≫ jH = jH ≫ ![𝟙 H, nH] k := fun k => by
    fin_cases k; exacts [(Category.id_comp _).trans (Category.comp_id _).symm, c₂]
  obtain ⟨t, ht, htv⟩ := exists_move_charts hL hM w hw ![𝟙 X, nX] ![𝟙 _, nU] ![𝟙 H, nH] ![N, -1] d₁ d₂ α hα
  have ee : ∀ k : Fin 2, e ≫ ![𝟙 H, nH] k = e := fun k => by fin_cases k; exacts [Category.comp_id _, c₄]
  have eeU : ∀ k : Fin 2, eU ≫ ![𝟙 _, nU] k = eU := fun k => by fin_cases k; exacts [Category.comp_id _, c₃]
  let σ : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => e) (fun _ => N - 1)) := ⟨fun i => rigM.s i ^ (N - 1)⟩
  have hσ : σ.IsGen := isGen_of_gm _ fun y i i' hi hi' => by
    refine (map_zpow _ _ _).trans ((congrArg (· ^ (N - 1)) (gen_trans hrigM (𝟙 _) y hi hi')).trans
      ((mul_zpow _ _ _).trans (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))
    simp only [trF, Fintype.prod_unique, zpow_one]
  obtain ⟨ρ, hρ, hρv⟩ := exists_gen hM (φ' := fun k : Fin 2 => e ≫ ![𝟙 H, nH] k) (ε' := ![N, -1])
    (fun G _ h => by
      simp only [ee, Fintype.prod_unique, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← zpow_add]; rfl) σ hσ
  obtain ⟨κ, ⟨hκ, hc⟩, -⟩ := GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hs hg he hP h₁ M hM
    (Fin 2) ![𝟙 H, nH] ![N, -1] t ρ ht hρ (corr_of_field hM (j ≫ e)
      (fun k => by rw [← Category.assoc, h₁, Category.assoc, ee]) (fun k => by rw [ee])
      fun F _ x z J' hJ' => by
        choose J hJ using fun χ : Sp F ⟶ X => exists_chart hL (χ z)
        rw [val_pull hJ', val_pull hJ', hρv _ _ z J' hJ']
        have q := htv _ (x ≫ eU) z (fun k => J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k))
          (fun k => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k))
          (fun k => by rw [d₁, ← Category.assoc]; exact hJ _) (fun k => by rw [d₂]; exact hJ' _)
        have q₁ : ∀ k : Fin 2, gw w ((x ≫ eU) ≫ ![𝟙 _, nU] k) z (J (((x ≫ eU) ≫ ψ) ≫ ![𝟙 X, nX] k))
            (fun _ => J' ((x ≫ eU) ≫ jH ≫ ![𝟙 H, nH] k)) = wv w (x ≫ eU) z J J' := fun k => by
          rw [Category.assoc (x ≫ eU) ψ, ← d₁, ← d₂, ← Category.assoc _ _ ψ, ← Category.assoc _ _ jH,
            Category.assoc x eU, eeU]
          rfl
        simp only [q₁] at q
        have q₂ : val α ((x ≫ eU) ≫ ψ) z J = _ * val t (x ≫ eU) z J' := q
        rw [Category.assoc, h₃, ← Category.assoc, hn _ _ z J hJ, hr F x z J J' hJ hJ', Fin.prod_univ_two] at q₂
        refine Eq.trans ?_ (map_zpow _ _ _).symm
        change _ = val rigM (x ≫ j) z J' ^ (N - 1)
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at q₂
        apply Additive.ofMul.injective
        replace q₂ := congrArg Additive.ofMul q₂
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at q₂ ⊢
        linear_combination (norm := module) -q₂)
  refine ⟨κ, hκ, fun Z r z a a' b b' ha ha' hb hb' => ?_⟩
  have hq : ∀ k : Fin 2, (r ≫ ![𝟙 _, nU] k ≫ jH) z ∈ M.U (![b, b'] k) := fun k => by
    fin_cases k; exacts [hb, hb']
  have q := htv _ r z ![a, a'] ![b, b'] (fun k => by fin_cases k; exacts [ha, ha']) hq
  rw [← hc, gm_pullGen M _ _ κ jH r z _ (Set.mem_iInter.2 fun k => by
    have := hq k
    rw [d₂] at this; exact this), Fin.prod_univ_two] at q
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id] at q
  rw [q, zpow_neg_one, mul_right_comm, inv_mul_cancel_right]

theorem exists_gen_mulRel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![((n : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig n α → ∃ κ, κ.IsGen ∧ Q.MulRel n α κ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hS n α hα hn
  have := ArithBase.ded (o := o) (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have : Nonempty U₀.toScheme := hS.ne.to_subtype
  have gq := isGrpPullback_pullback ρ.P.A Q.u₀
  let eU : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ := η[(Over.pullback Q.u₀).obj ρ.P.A].left
  let nU : pullback ρ.P.A.hom Q.u₀ ⟶ pullback ρ.P.A.hom Q.u₀ := (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n).left
  have h₁ : eU ≫ Q.φ = U₀.ι ≫ eSec Q.G := one_comm Q.cart
  have h₃ : eU ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := one_comm gq
  have c₁ : nU ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (mulA ρ.P.A n).left := mulA_comm gq n
  have c₅ : nU ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n)
  have rg : ∀ {F : Type} [Field F] {Y : Scheme.{0}} (g : Sp F ⟶ Y) (V : Y.Opens) (z : Sp F), g z ∈ V →
      Set.range g ⊆ V := fun g V z hz => by
    rintro _ ⟨y, rfl⟩
    exact (top_le_iff_mem g V z).2 hz (x := y) trivial
  obtain ⟨κ, hκ, H⟩ := core hS.normal U₀.ι Q.G.hom (eSec Q.G) Q.φ _ eU Q.semi.smooth
    (grpObj_geometricallyIntegral_of_smooth _ Q.G) (Over.w η[Q.G]) Q.cart.1 h₁ ρ.P.isLB Q.L.isLB (eSec ρ.P.A) Q.u₀
    (pullback.fst _ _) h₃ (mulA Q.G n).left nU (mulA ρ.P.A n).left c₁ (mulA_comm Q.cart n) (one_mulA n) (one_mulA n)
    Q.w Q.w_gen ρ.rig Q.L.rig Q.L.rigGen ((n : ℤ) ^ 2) α hα (fun Z t z J hJ => by
      have q := val_corr hJ hn t
      rw [val_pull hJ, val_mul hJ, val_inv] at q
      exact q.trans (congrArg (· * _) (map_zpow _ _ _))) (fun F _ x z J J' hJ hJ' => by
      have e₁ : (x ≫ eU) ≫ Q.φ = (x ≫ U₀.ι) ≫ eSec Q.G := by rw [Category.assoc, h₁, Category.assoc]
      have e₃ : (x ≫ eU) ≫ pullback.fst _ _ = (x ≫ Q.u₀) ≫ eSec ρ.P.A := by rw [Category.assoc, h₃, Category.assoc]
      have q := congrArg (toStk z) (Q.w_rig F (x ≫ eU) (x ≫ U₀.ι) (x ≫ Q.u₀) _ _ e₁ e₃ (rg _ _ z (hJ _))
        (rg _ _ z (hJ' _)))
      rw [map_mul, toStk_valF _ _ z (mem_pull.2 (by have := hJ ((x ≫ eU) ≫ pullback.fst _ _); rwa [e₃] at this ⊢)),
        toStk_valF (x ≫ eU) _ z (And.intro (mem_pull.2 (hJ ((x ≫ eU) ≫ pullback.fst _ _)))
          (mem_pull.2 (hJ' ((x ≫ eU) ≫ Q.φ)))),
        toStk_valF _ _ z (mem_pull.2 (by have := hJ' ((x ≫ eU) ≫ Q.φ); rwa [e₁] at this ⊢))] at q
      rw [val_of _ _ z J (fun _ => J ((x ≫ eU) ≫ pullback.fst _ _)) (fun _ => by rw [e₃]),
        val_of _ _ z J' (fun _ => J' ((x ≫ eU) ≫ Q.φ)) (fun _ => by rw [e₁])]
      exact Units.ext q)
  refine ⟨κ, hκ, fun K _ g g' jP jP' jL jL' k₁ k₂ m₁ m₂ m₃ m₄ => ?_⟩
  obtain rfl : g' = g ≫ nU := pullback.hom_ext (by rw [k₁, Category.assoc, c₁]) (by rw [k₂, Category.assoc, c₅])
  have z : Sp K := IsLocalRing.closedPoint _
  have a₁ := m₁ ⟨z, rfl⟩
  have a₂ := m₂ ⟨z, rfl⟩
  have a₃ := m₃ ⟨z, rfl⟩
  have a₄ := m₄ ⟨z, rfl⟩
  have q := congrArg Units.val (H _ g z jP jP' jL jL' a₁ a₃ a₂ a₄)
  have pw : ∀ {G : Type} [Group G] (x : G), x ^ ((n : ℤ) ^ 2) = x ^ (n ^ 2) := fun x => by
    rw [← Nat.cast_pow, zpow_natCast]
  rw [pw] at q
  refine (toStk z).injective ?_
  rw [map_mul, map_mul, map_pow, toStk_valF _ _ z (Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact a₁
      · rw [Category.assoc, c₁] at a₃; exact a₃),
    toStk_valF (g ≫ nU) _ z (And.intro (mem_pull.2 a₃) (mem_pull.2 a₄)),
    toStk_valF g _ z (And.intro (mem_pull.2 a₁) (mem_pull.2 a₂)),
    toStk_valF _ _ z (Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact a₂
      · rw [Category.assoc, show nU ≫ Q.φ = _ from mulA_comm Q.cart n] at a₄; exact a₄)]
  exact q

end GlobalTheory.ZH.MulExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFibreSectionOfModelSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GenSec
open GlobalTheory.Points

theorem sec_up {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (hL : L.IsLB) (hL' : L'.IsLB) (m : Y ⟶ X') (p : Y ⟶ X) (hp : m ≫ F = p) (τ : ∀ k, Γ(Y, m ⁻¹ᵁ L'.U k))
    (hτ : ∀ (y : Y) k k', m y ∈ L'.U k → m y ∈ L'.U k' →
      gs (𝟙 Y) y _ (τ k) = (gm m y (L'.U k ⊓ L'.U k') (L'.g k k')).val * gs (𝟙 Y) y _ (τ k')) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)),
      ∀ (K : Type) [Field K] (q : Sp K ⟶ Y) j k, ⊤ ≤ (q ≫ m) ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k) →
        valR q _ (s.f fun _ => j) = valR (q ≫ m) _ (w.s (fun _ => j, k)).val * valR q _ (τ k) := by
  subst hp
  let W : L.ι → L'.ι → Y.Opens := fun j k => m ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
  have leU : ∀ (J : Fin 1 → L.ι) k, W (J 0) k ≤ LB.wchart L (fun _ : Fin 1 => m ≫ F) J := fun J k y hy =>
    Set.mem_iInter.2 fun i => by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact mem_pull.1 hy.1
  have leT : ∀ j k, W j k ≤ m ⁻¹ᵁ L'.U k := fun j k y hy => hy.2
  let u : ∀ j k, Γ(Y, W j k) := fun j k =>
    (m.app ((L.pull F).U (fun _ => j) ⊓ L'.U k)).hom (w.s (fun _ => j, k)).val * resG Y (leT j k) (τ k)
  have hu : ∀ j k (y : Y), y ∈ W j k → gs (𝟙 Y) y _ (u j k) = (gw w m y j k).val * gs (𝟙 Y) y _ (τ k) :=
    fun j k y hy => (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_pull (𝟙 Y) m y _ hy _).trans (by rw [Category.id_comp]; exact gs_unit m y _ hy _)) (gs_res _ y _ hy _))
  have glue : ∀ J : Fin 1 → L.ι, ∃ a : Γ(Y, LB.wchart L (fun _ : Fin 1 => m ≫ F) J),
      ∀ k, resG Y (leU J k) a = u (J 0) k := by
    intro J
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (W (J 0)) (LB.wchart L (fun _ : Fin 1 => m ≫ F) J)
      (fun k => homOfLE (leU J k)) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' (m y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.2 (Set.mem_iInter.1 hy 0), hk⟩) (u (J 0))
      (fun k k' => fn_ext (V := W (J 0) k ⊓ W (J 0) k') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have hj : F (m y) ∈ L.U (J 0) := mem_pull.1 hy.1.1
        rw [hu _ _ y hy.1, hu _ _ y hy.2, hτ y k k' hy.1.2 hy.2.2, hw _ m y _ _ k k' hj hj hy.1.2 hy.2.2,
          gm_self hL (m ≫ F) y hj, _root_.one_mul, ← _root_.mul_assoc, ← Units.val_mul, mul_right_comm,
          inv_mul_cancel, _root_.one_mul])
    exact ⟨a, ha⟩
  choose a ha using glue
  refine ⟨⟨a, fun J J' => fn_ext fun y hy => ?_⟩, fun K _ q j k hq => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' (m y)
    have hj : F (m y) ∈ L.U (J 0) := Set.mem_iInter.1 hy.1 0
    have hj' : F (m y) ∈ L.U (J' 0) := Set.mem_iInter.1 hy.2 0
    have key : ∀ I : Fin 1 → L.ι, F (m y) ∈ L.U (I 0) →
        gs (𝟙 Y) y _ (a I) = (gw w m y (I 0) k).val * gs (𝟙 Y) y _ (τ k) := fun I hI => by
      have hy' : y ∈ W (I 0) k := ⟨mem_pull.2 hI, hk⟩
      exact (gs_res (𝟙 Y) y (leU I k) hy' _).symm.trans ((congrArg (gs (𝟙 Y) y _) (ha I k)).trans (hu _ _ y hy'))
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y J J' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (key J hj).trans (Eq.trans ?_ (congrArg _ (key J' hj')).symm)
    rw [hw _ m y _ _ k k hj hj' hk hk, gm_self hL' m y hk, inv_one, _root_.mul_one, Units.val_mul, _root_.mul_assoc,
      Fin.prod_univ_one, zpow_one, Category.id_comp]
  · have hq' : ⊤ ≤ q ⁻¹ᵁ W j k := hq
    refine (valR_res q (leU (fun _ => j) k) hq' _).symm.trans ((congrArg (valR q _) (ha (fun _ => j) k)).trans ?_)
    exact (valR_mul q _ hq' _ _).trans (congrArg₂ (· * ·) (valR_comp q m _ _).symm (valR_res q _ hq' _))

theorem sec_up_secOn {X X' Y G : Scheme.{0}} {L : LB X} {M : LB G} {F : X' ⟶ X} {φ : X' ⟶ G}
    {w : LB.Iso (M.pull φ) (L.pull F)} (hw : w.IsGen) (hL : L.IsLB) (hM : M.IsLB) (m : Y ⟶ X') (p : Y ⟶ X)
    (hp : m ≫ F = p) (V : G.Opens) (hV : ∀ y, (m ≫ φ) y ∈ V)
    (σ : ∀ j, Γ(G, V ⊓ (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)).U j))
    (hσ : σ ∈ secOn (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)) V) :
    ∃ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => 1)),
      ∀ (K : Type) [Field K] (q : Sp K ⟶ Y) j k, Set.range ((q ≫ m) ≫ F) ⊆ L.U j → Set.range ((q ≫ m) ≫ φ) ⊆ M.U k →
        valR q _ (s.f fun _ => j) =
          valR (q ≫ m) _ (w.s (fun _ => j, fun _ => k)).val * valR ((q ≫ m) ≫ φ) _ (σ fun _ => k) := by
  let O : LB G := LB.LinComb M (K := Fin 1) (fun _ => 𝟙 G) (fun _ => 1)
  have le : ∀ k : PUnit → M.ι, m ⁻¹ᵁ (M.pull φ).U k ≤ (m ≫ φ) ⁻¹ᵁ (V ⊓ O.U fun _ => k PUnit.unit) :=
    fun k y hy => ⟨hV y, Set.mem_iInter.2 fun _ => (mem_pull (F := φ) (x := m y)).1 hy⟩
  have val : ∀ (y : Y) (k : PUnit → M.ι), m y ∈ (M.pull φ).U k →
      gs (𝟙 Y) y _ (((m ≫ φ).appLE _ _ (le k)).hom (σ fun _ => k PUnit.unit)) =
        gs (m ≫ φ) y _ (σ fun _ => k PUnit.unit) := fun y k hk =>
    (gs_res (𝟙 Y) y (le k) hk _).trans ((gs_pull (𝟙 Y) (m ≫ φ) y _ (le k hk) _).trans (by rw [Category.id_comp]))
  obtain ⟨s, hs⟩ := sec_up ((isGen_iff w).1 hw) hL (pull_isLB hM φ) m p hp
    (fun k => ((m ≫ φ).appLE _ _ (le k)).hom (σ fun _ => k PUnit.unit)) (fun y k k' hk hk' => by
      have hm : (m ≫ φ) y ∈ (V ⊓ O.U fun _ => k PUnit.unit) ⊓ O.U fun _ => k' PUnit.unit := ⟨le k hk, (le k' hk').2⟩
      have hm' : (m ≫ φ) y ∈ (O.U fun _ => k PUnit.unit) ⊓ O.U fun _ => k' PUnit.unit := ⟨hm.1.2, hm.2⟩
      rw [val y k hk, val y k' hk', gm_pull_g M φ m y k k' hk hk']
      refine (gs_res _ y _ hm _).symm.trans ((congrArg (gs (m ≫ φ) y _) (hσ _ _)).trans ((gs_mul _ y _ hm _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ y _ hm _).trans ((gs_unit _ y _ hm' _).trans (congrArg Units.val
          ((gm_linComb M _ _ (m ≫ φ) y _ _ hm.1.2 hm.2).trans ?_)))) (gs_res _ y _ hm _))))
      rw [Fin.prod_univ_one, zpow_one, Category.comp_id])
  refine ⟨s, fun K _ q j k hj hk => ?_⟩
  have hk' : ⊤ ≤ q ⁻¹ᵁ (m ⁻¹ᵁ (M.pull φ).U fun _ => k) := fun z _ => mem_pull.2 (hk ⟨z, rfl⟩)
  refine (hs K q j (fun _ => k) fun z hz => ⟨mem_pull.2 (hj ⟨z, rfl⟩), hk' hz⟩).trans (congrArg _ ?_)
  exact (valR_appLE q (m ≫ φ) (le fun _ => k) hk' _).trans (by rw [Category.assoc])

theorem exists_generic_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (eta : Sp Ω ⟶ U₀.toScheme), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → (N : Set M.Z).Nonempty → eta ≫ U₀.ι = M.pt → ∃ s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R))), ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP : ρ.P.L.ι) (jL : Q.L.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → g ≫ pullback.fst _ _ = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → g ≫ pullback.snd _ _ = spMap β ≫ eta → Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL → valF q _ (s.f fun _ => jP) = valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val * valF (g ≫ Q.φ) _ (σ fun _ => jL) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q N σ eta hσ hN heta
  have hw : (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ ρ.P.A.hom =
      ((fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ eta) ≫ Q.u₀ := by
    rw [Category.assoc, Q.u₀_gen eta heta, Over.w]
    exact (Over.w (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A)).symm
  have hc : Q.φ ≫ Q.G.hom = pullback.snd ρ.P.A.hom Q.u₀ ≫ U₀.ι := Q.cart.1.w
  have hb : (pullback.lift _ _ hw ≫ Q.φ) ≫ Q.G.hom =
      (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left ≫ M.pt := by
    rw [Category.assoc, hc, pullback.lift_snd_assoc, Category.assoc, heta]
  obtain ⟨s, hs⟩ := sec_up_secOn Q.w_gen ρ.P.isLB Q.L.isLB (pullback.lift _ _ hw) _ (pullback.lift_fst _ _ _)
    (Q.G.hom ⁻¹ᵁ N) (fun y => by
      show ((pullback.lift _ _ hw ≫ Q.φ) ≫ Q.G.hom) y ∈ N
      rw [hb]
      exact M.top_le_preimage_pt hN (x := (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left y)
        trivial) σ hσ
  refine ⟨s, fun K _ β q g jP jL h₁ h₂ h₃ hP hL => ?_⟩
  obtain rfl : g = q ≫ pullback.lift _ _ hw := by
    refine pullback.hom_ext ?_ ?_
    · rw [h₂, Category.assoc, pullback.lift_fst]
    · rw [h₃, Category.assoc, pullback.lift_snd, ← Category.assoc, h₁]
  exact hs K q jP jL hP hL

end GlobalTheory.ZH.GenSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSectionsFromIntegralModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.IntegralCarry
open GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH.ParTranslate GlobalTheory.ThetaSpecialise

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

theorem expandsG_extend
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) : U.ExpandsG F k (extendSec U F k (genericSec U k σ)) s := by
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm

theorem famOf_zero (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) (α : D.toPre.X) (h : ∀ j, (f α).f j = 0) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := (0 : Fam D.toPre F k).s α) D.toPre.P.isLB (fun y J hJ => ?_) j
  refine (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm.trans (Eq.trans ?_ (sval_zero' (π := famBase D.toPre F) hJ _).symm)
  exact (gs_eq _ _ _ (hJ.mem _ _) _).trans ((congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _))

theorem crd_carries (w : W0 U) {J : Type}
    (σ : J → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (t : J → SecA A F k) (ht : ∀ i, Carries U F k w (t i) (extendSec U F k (genericSec U k (σ i))))
    (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (v : J → F)
    (h : Crd _ σ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) v) :
    Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) v := by
  obtain ⟨l', c, hl', hv⟩ := h
  obtain ⟨l, rfl⟩ : ∃ l : U.LG.L.ι, l' = fun _ : Fin 1 => l := ⟨l' 0, funext fun i => congrArg l' (Subsingleton.elim _ _)⟩
  let y : Sp F := IsLocalRing.closedPoint F
  let x : Sp F ⟶ G.left := a.left ≫ pullback.fst G.hom (jK R)
  have m : x y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => l) := (top_le_iff_mem _ _ y).1 hl'
  have m₀ : x y ∈ U.LG.L.U l := mem_wchart.1 m 0
  obtain ⟨J₀, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨d, hd⟩ := exists_unit_carries U F k w a l ((top_le_iff_mem x _ y).2 m₀) y J₀ hJ
  obtain ⟨d₀, hd₀⟩ := toStk_onto y d.val
  have hd₁ : d₀ ≠ 0 := fun h0 => by
    have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd₀
    exact Units.ne_zero _ hd₀.symm
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) = x := by
    rw [e₀]
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := e₁ ▸ m₀
  have m' := hJ.mem (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) r'
  refine ⟨fun _ : Fin 1 => J₀ (r' ≫ (snd (TFK (R := R) F) A.A).left), c * Units.mk0 d₀ hd₁,
    (top_le_iff_mem r' _ y).2 m', fun i => ?_⟩
  rw [hv i, Units.val_mul, _root_.mul_assoc, Units.val_mk0]
  refine congrArg _ ((toStk y).injective ?_)
  rw [map_mul, hd₀]
  refine (toStk_valF_gs x _ y m _).trans (Eq.trans ?_ ((hd _ _ (ht i)).trans
    (congrArg _ (toStk_valF_gs r' _ y m' _).symm)))
  refine Eq.symm ((toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans ?_)
  rw [← e₁]
  exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k (σ i)) r y (fun _ => l)
      (fun _ => m₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) (σ i) _ y (fun _ => l) (fun _ => m₂))

end

theorem exists_carry : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k J σ f hE hf w₀ hw₀
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) k, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hf i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D k s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  choose t ht using fun i => exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀
    (extendSec u.U.toUnifPre (PadicAlgCl p) k (genericSec u.U.toUnifPre k (σ i)))
  exact ⟨t, s, fun i => ⟨_, ht i, expandsG_extend _ _ k (σ i) (f i) (hE i) (s i) (hs i)⟩,
    fun i α h j => famOf_zero _ k (f i) (s i) (hs i) α h j,
    fun a v h => crd_carries u.U.toUnifPre _ k w₀ σ t ht a v h⟩

end GlobalTheory.ZH.IntegralCarry
end
end

