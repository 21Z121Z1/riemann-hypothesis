import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsRigNorm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsClosedEmbeddingOfAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedCharts
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormsOfTests
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section

namespace GlobalTheory.ZJ.TestNorm

open CubeGen

variable {p : ℕ} [Fact p.Prime]

section Cube

variable {C : Core} {T : C.Theta} {y : Sp (OO p) ⟶ C.Z} {τ : C.Test y} (E : T.Ext τ)

theorem cube_eq_one (hp : IsPullback τ.f τ.H.hom C.GG.hom τ.y₀) (x : Sp (PadicAlgCl p) ⟶ (G3 C.A).left)
    (s : Fin 3 → (Sp (OO p) ⟶ C.G.toScheme)) (hs : ∀ k, s k ≫ C.GG.hom = y)
    (hx : ∀ k, gPt p ≫ s k = (x ≫ (x3 C.A k).left) ≫ C.a) :
    ∃ (c : thK.{0} → (Sp (OO p) ⟶ τ.H.left)) (q : thK.{0} → (Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V))),
      (∀ I, IsLift τ (c I) (q I) ∧ q I ≫ τ.φ = x ≫ thφ C.A (x3 C.A) I) ∧
      ∀ (a : thK.{0} → E.L.L.ι) (b : thK.{0} → T.L.L.ι), (∀ I, c I (cPt p) ∈ E.L.L.U (a I)) →
        (∀ I, (x ≫ thφ C.A (x3 C.A) I) (z₀ p) ∈ T.L.L.U (b I)) →
        un p (gm x (z₀ p) (LB.wchart T.L.L (thφ C.A (x3 C.A)) b) (T.cub.t.s b)) *
          ∏ I, wv E.w (q I) (a I) (b I) ^ thε I = 1 := by
  have hG := τ.isSemiAbelian
  have := hG.smooth
  have := hG.geomConnected
  have := smooth_cube_hom τ.H
  have := geometricallyIntegral_cube_hom τ.H
  have : IsCommMonObj ((Over.pullback (Out.jK τ.V)).obj τ.H) := Functor.isCommMonObj_obj
  have : Mono (jg τ) :=
    have := DvrModel.isOpenImmersion_generic (IsPullback.of_hasPullback τ.H.hom (Out.jK τ.V))
    inferInstance
  let HK := (Over.pullback (Out.jK τ.V)).obj τ.H
  have gp := isGrpPullback_pullback τ.H (Out.jK τ.V)
  have hK := isPullback_cube gp
  have h₁ : ∀ I : thK.{0}, thφ HK (x3 HK) I ≫ jg τ = (cubeMapOf gp).F3 ≫ thφ τ.H (x3 τ.H) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  have h₂ : ∀ I : thK.{0}, thφ HK (x3 HK) I ≫ τ.φ = (cubeMapOf τ.φ_cart).F3 ≫ thφ C.A (x3 C.A) I :=
    fun I => (cubeMapOf τ.φ_cart).psum_comm I.down
  obtain ⟨r, hr⟩ := exists_frac τ
  have lifts : ∀ (x : Sp (PadicAlgCl p) ⟶ (G3 C.A).left) (s : Fin 3 → (Sp (OO p) ⟶ C.G.toScheme)),
      (∀ k, s k ≫ C.GG.hom = y) → (∀ k, gPt p ≫ s k = (x ≫ (x3 C.A k).left) ≫ C.a) →
      ∃ (c : Sp (OO p) ⟶ (G3 τ.H).left) (q : Sp (PadicAlgCl p) ⟶ (G3 HK).left), c ≫ (G3 τ.H).hom = spMap τ.j ∧
        q ≫ (cubeMapOf gp).F3 = gPt p ≫ c ∧ q ≫ (cubeMapOf τ.φ_cart).F3 = x ∧
        ∀ I : thK.{0}, IsLift τ (c ≫ thφ τ.H (x3 τ.H) I) (q ≫ thφ HK (x3 HK) I) ∧
          (q ≫ thφ HK (x3 HK) I) ≫ τ.φ = x ≫ thφ C.A (x3 C.A) I := by
    intro x s hs hx
    choose c q k₁ k₂ k₃ using fun k => exists_lift τ (hs k) (hx k)
    let d : Fin 3 → (Over.mk (spMap τ.j) ⟶ τ.H) := fun k => Over.homMk (c k) (k₁ k).1
    let l : Over.mk (spMap τ.j) ⟶ G3 τ.H := lift (d 0) (lift (d 1) (d 2))
    have lx : ∀ k, l ≫ x3 τ.H k = d k := fun k => by fin_cases k <;> simp [l, x3]
    have lx' : ∀ k, l.left ≫ (x3 τ.H k).left = c k := fun k => congrArg (fun z => z.left) (lx k)
    have w : l.left ≫ (G3 τ.H).hom = spMap τ.j := Over.w l
    let Q : Sp (PadicAlgCl p) ⟶ (G3 HK).left := hK.lift (gPt p ≫ l.left) r
      ((Category.assoc _ _ _).trans ((congrArg (gPt p ≫ ·) w).trans hr))
    have hQ : Q ≫ (cubeMapOf gp).F3 = gPt p ≫ l.left := hK.lift_fst _ _ _
    have hQ' : ∀ k, Q ≫ (x3 HK k).left = q k := fun k => (cancel_mono (jg τ)).1
      ((Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (cubeMap_comp_proj_three (cubeMapOf gp) k).symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hQ).trans ((Category.assoc _ _ _).trans
          ((congrArg (gPt p ≫ ·) (lx' k)).trans (k₁ k).2.symm))))))
    have hx' : Q ≫ (cubeMapOf τ.φ_cart).F3 = x := hom_ext_triple _ fun k =>
      (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (cubeMap_comp_proj_three (cubeMapOf τ.φ_cart) k)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.φ) (hQ' k)).trans (k₃ k))))
    refine ⟨l.left, Q, w, hQ, hx', fun I => ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (l.left ≫ ·) (Over.w (psum τ.H (x3 τ.H) I.down))).trans w)
    · exact (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (h₁ I)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hQ).trans (Category.assoc _ _ _))))
    · exact (Category.assoc _ _ _).trans ((congrArg (Q ≫ ·) (h₂ I)).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) hx')))
  obtain ⟨c, q, k₁, k₂, rfl, k₄⟩ := lifts x s hs hx
  refine ⟨_, _, k₄, fun a b ha hb => ?_⟩
  let u : Sp (PadicAlgCl p) ⟶ C.U.toScheme := r ≫ τ.yK
  have hu : u ≫ C.U.ι = gPt p ≫ y := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← hr, Category.assoc, τ.fac]
  let o : Over.mk u ⟶ C.A := 1
  have ho : o.left = u ≫ eSec C.A := by
    show (toUnit _ ≫ η[C.A]).left = _
    simp [eSec]
  have ox : ∀ k, lift o (lift o o) ≫ x3 C.A k = o := fun k => by fin_cases k <;> simp [x3]
  have oI : ∀ I : thK.{0}, (lift o (lift o o)).left ≫ thφ C.A (x3 C.A) I = o.left := fun I => by
    have e : lift o (lift o o) ≫ psum C.A (x3 C.A) I.down = psum C.A (fun _ => o) I.down :=
      (psum_hom (preHom (lift o (lift o o))) (x3 C.A) I.down).trans (congrArg (psum C.A · I.down) (funext ox))
    have e' : psum C.A (fun _ : Fin 3 => o) I.down = o := (psum_hom (1 : (Over.mk u ⟶ C.A) →* (Over.mk u ⟶ C.A))
      (fun _ => o) I.down).symm
    exact congrArg (fun z => z.left) (e.trans e')
  obtain ⟨c₀, q₀, m₁, m₂, m₃, m₄⟩ := lifts (lift o (lift o o)).left (fun _ => y ≫ C.e)
    (fun _ => (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) C.e_sec).trans (Category.comp_id _))) (fun k => by
      refine Eq.trans ?_ (congrArg (fun z => z.left ≫ C.a) (ox k)).symm
      rw [ho, ← Category.assoc, ← hu, Category.assoc, C.e_zero]
      exact (Category.assoc _ _ _).symm)
  have same := fun I => (m₄ I).1.unique hp (m₄ ⟨∅⟩).1 ((m₄ I).2.trans ((oI I).trans ((m₄ _).2.trans (oI _)).symm))
  obtain ⟨a₀, ha₀⟩ := exists_chart E.L.isLB ((c₀ ≫ thφ τ.H (x3 τ.H) (⟨∅⟩ : thK.{0})) (cPt p))
  choose J hJ using fun χ : Sp (PadicAlgCl p) ⟶ C.A.left => exists_chart T.L.isLB (χ (z₀ p))
  have key := gen_wv_eq E.L.isLB T.L.isLB E.w_gen hK (lift η[τ.H] (lift η[τ.H] η[τ.H])).left (Over.w _)
    (thφ τ.H (x3 τ.H)) (thφ HK (x3 HK)) (thφ C.A (x3 C.A)) (cubeMapOf τ.φ_cart).F3 h₁ h₂ (ε := thε) (t := T.cub.t)
    T.cub.isGen k₂ m₂ (k₁.trans m₁.symm) (a := a) (a' := fun _ => a₀) (b := b) (b' := fun _ => J o.left) ha
    (fun I => by rw [(same I).1]; exact ha₀) hb (fun I => by rw [m₃, oI]; exact hJ _)
  refine key.trans ?_
  have e₁ : gm (lift o (lift o o)).left (z₀ p) (LB.wchart T.L.L (thφ C.A (x3 C.A)) fun _ => J o.left)
      (T.cub.t.s fun _ => J o.left) = 1 :=
    (val_of (φ := thφ C.A (x3 C.A)) (ε := thε) T.cub.t _ _ J _ fun I => congrArg J (oI I)).symm.trans
      ((isCub_cubV T.cub (T := Over.mk u) hJ).face 1 1)
  rw [m₃]
  erw [e₁]
  rw [map_one, _root_.one_mul, Finset.prod_congr rfl fun I _ => by rw [(same I).2]]
  exact prod_thε (wv_pos _ _ _ _)

end Cube

end GlobalTheory.ZJ.TestNorm

namespace GlobalTheory.ZJ

open TestNorm CubeGen

theorem Core.Theta.exists_norms : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta), C.HasTests → T.BTest L → ∃ ν, T.Norms (T.Om L) ν := by
  intro hE C L T hT hB
  have hC : C.TestCart := fun p _ y τ => (L.test p y τ).1
  have sepG : IsSeparated C.GG.hom := (core_basic C).1
  have ex : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), C.Cl y →
      ∃ (τ : C.Test y) (E : T.Ext τ) (ρ : ℝ), 0 < ρ ∧ IsRigNorm E ρ := fun p _ y hy => by
    obtain ⟨τ⟩ := hT p y hy
    obtain ⟨E⟩ := Core.Theta.nonempty_ext hE C T p y τ hC
    exact ⟨τ, E, exists_isRigNorm E (hC p y τ)⟩
  choose τ E ρ hρ hR using ex
  have ex₂ : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left), ∃ n : T.L.L.ι → ℝ, (∀ j, 0 < n j) ∧
      (∀ j j', x (z₀ p) ∈ T.L.L.U j → x (z₀ p) ∈ T.L.L.U j' →
        un p (gm x (z₀ p) _ (T.L.L.g j j')) * n j = n j') ∧
      ∀ j t, (∃ (y : Sp (OO p) ⟶ C.Z) (hy : C.Cl y), ∃ c q a, IsLift (τ p y hy) c q ∧ q ≫ (τ p y hy).φ = x ∧
        c (cPt p) ∈ (E p y hy).L.L.U a ∧ x (z₀ p) ∈ T.L.L.U j ∧ t = wv (E p y hy).w q a j / ρ p y hy) → n j = t := by
    intro p _ x
    refine exists_norm_ext T.L.isLB x _ ?_ ?_
    · rintro j t ⟨y, hy, c, q, a, -, -, -, h, rfl⟩
      exact ⟨div_pos (wv_pos _ _ _ _) (hρ p y hy), h⟩
    · rintro j t j' t' ⟨y, hy, c, q, a, h₁, rfl, h₃, h₄, rfl⟩ ⟨y', hy', c', q', a', k₁, k₂, k₃, k₄, rfl⟩
      obtain rfl : y = y' := base_ext (by rw [← h₁.base, ← k₁.base, k₂])
      obtain ⟨rfl, rfl⟩ := h₁.unique (hC _ _ _) k₁ k₂.symm
      rw [← wv_trans (E p y hy).w_gen h₁.2 h₃ k₃ h₄ k₄, mul_div_assoc]
  choose ν h₁ h₂ h₃ using ex₂
  have hν : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (hy : C.Cl y) c q a j, IsLift (τ p y hy) c q →
      c (cPt p) ∈ (E p y hy).L.L.U a → (q ≫ (τ p y hy).φ) (z₀ p) ∈ T.L.L.U j →
      ν p (q ≫ (τ p y hy).φ) j = wv (E p y hy).w q a j / ρ p y hy :=
    fun p _ y hy c q a j k₁ k₂ k₃ => h₃ p _ j _ ⟨y, hy, c, q, a, k₁, rfl, k₂, k₃, rfl⟩
  have cl : ∀ {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} {u : Sp (PadicAlgCl p) ⟶ C.U.toScheme},
      gPt p ≫ y = u ≫ C.U.ι → C.Cl y := fun {p} _ {y u} h => by
    rw [Core.Cl, h]
    exact range_comp_ι_subset _ _
  have bas : ∀ {p : ℕ} [Fact p.Prime] {b : Sp (OO p) ⟶ C.G.toScheme} {x : Sp (PadicAlgCl p) ⟶ C.A.left},
      gPt p ≫ b = x ≫ C.a → gPt p ≫ b ≫ C.GG.hom = (x ≫ C.A.hom) ≫ C.U.ι := fun {p} _ {b x} h => by
    rw [← Category.assoc, h, Category.assoc, C.isPullback_a.w, Category.assoc]
  refine ⟨ν, ⟨h₁, fun p _ x i j hi hj => ?_, fun p _ s j hj => ?_⟩, fun p _ u ⟨y, hu, _⟩ J hJ => ?_,
    fun p _ x hx J hJ => ?_, fun p _ u => ?_⟩
  · have hi' := (range_subset_iff x (z₀ p) _).1 hi
    have hj' := (range_subset_iff x (z₀ p) _).1 hj
    rw [← un_gm x (U := T.L.L.U i ⊓ T.L.L.U j) ⟨hi', hj'⟩]
    exact h₂ p x i j hi' hj'
  · have e : gPt p ≫ s ≫ C.a = (gPt p ≫ s) ≫ C.a := (Category.assoc _ _ _).symm
    have hy := cl (bas e)
    obtain ⟨c, q, k₁, k₂, k₃⟩ := exists_lift (τ p _ hy) rfl e
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    rw [← k₃, hν p _ hy c q a j k₁ ha (by rw [k₃]; exact gen_mem s hj), (hR p _ hy).integral k₁ k₂ ha hj,
      div_self (hρ p _ hy).ne']
  · have hy := cl hu
    obtain ⟨c, q, k₁, k₂, k₃⟩ := exists_lift (τ p y hy) (b := y ≫ C.e) (x := u ≫ eSec C.A)
      ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) C.e_sec).trans (Category.comp_id _))) (by
        rw [← Category.assoc, hu, Category.assoc, C.e_zero]
        exact (Category.assoc _ _ _).symm)
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    have hJ' := (range_subset_iff u (z₀ p) _).1 hJ
    have hb : (q ≫ (τ p y hy).φ) (z₀ p) ∈ T.L.L.U (J ⟨⟩) := by
      rw [k₃]
      exact Set.mem_iInter.1 hJ' ⟨⟩
    have e₁ := hν p y hy c q a _ k₁ ha hb
    have e₂ := hR p y hy c q u a _ k₁ k₃ ha hb
    rw [k₃] at e₁
    rw [Fintype.prod_unique, zpow_one]
    refine (congrArg₂ (· * ·) (un_gm u hJ' _).symm e₁).trans ?_
    rw [← mul_div_assoc]
    exact (div_eq_one_iff_eq (hρ p y hy).ne').2 e₂
  · choose s hs _ using hx
    have e : ∀ k, gPt p ≫ s k ≫ C.GG.hom = (x ≫ (G3 C.A).hom) ≫ C.U.ι := fun k => by
      rw [bas (hs k), Category.assoc x, Over.w]
    have hy := cl (e 0)
    obtain ⟨c, q, k₁, k₂⟩ := cube_eq_one (E p _ hy) (hC _ _ _) x s (fun k => base_ext ((e k).trans (e 0).symm)) hs
    choose a ha using fun I => exists_chart (E p _ hy).L.isLB (c I (cPt p))
    have hJ' := (range_subset_iff x (z₀ p) _).1 hJ
    have hb : ∀ I, (x ≫ thφ C.A (x3 C.A) I) (z₀ p) ∈ T.L.L.U (J I) := Set.mem_iInter.1 hJ'
    refine (congrArg₂ (· * ·) (un_gm x hJ' _).symm (Finset.prod_congr rfl fun I _ => congrArg (· ^ thε I)
      ((congrArg (ν p · (J I)) (k₁ I).2.symm).trans
        (hν p _ hy _ _ (a I) (J I) (k₁ I).1 (ha I) (by rw [(k₁ I).2]; exact hb I))))).trans ?_
    simp only [div_zpow, Finset.prod_div_distrib]
    exact (congrArg (_ * ·) ((congrArg (_ / ·) (prod_thε (hρ p _ hy))).trans (div_one _))).trans (k₂ a J ha hb)
  · by_cases h : ∃ y : Sp (OO p) ⟶ C.Z, gPt p ≫ y = u ≫ C.U.ι
    swap
    · exact ⟨1, one_pos, fun x j hx _ ⟨b, hb, _⟩ => absurd ⟨_, hx ▸ bas hb⟩ h⟩
    obtain ⟨y, hu⟩ := h
    have hy := cl hu
    refine ⟨1 / ρ p y hy, one_div_pos.2 (hρ p y hy), fun x j hx hj ⟨b, hb, _⟩ => ?_⟩
    obtain ⟨c, q, k₁, k₂, rfl⟩ := exists_lift (τ p y hy) (base_ext ((bas hb).trans (by rw [hx, hu]))) hb
    obtain ⟨a, ha⟩ := exists_chart (E p _ hy).L.isLB (c (cPt p))
    have hj' := (range_subset_iff _ (z₀ p) _).1 hj
    obtain ⟨t₁, t₂⟩ := k₁.theta (E p y hy) ha hj'
    rw [hν p y hy c q a j k₁ ha hj', ← mul_div_assoc]
    refine ⟨div_le_div_of_nonneg_right t₁ (hρ p y hy).le, (div_left_inj' (hρ p y hy).ne').trans (t₂.trans
      ((hB p y _ (E p y hy) _ k₁.centre).symm.trans ?_))⟩
    have e : (τ p y hy).f (c (cPt p)) = b (cPt p) := congrArg (fun g => g (cPt p)) k₂
    rw [e]
    refine ⟨fun h => ⟨b, hb, h⟩, fun ⟨b', hb', h⟩ => ?_⟩
    rwa [ext_gPt C.GG.hom (base_ext ((bas hb).trans (bas hb').symm)) (hb.trans hb'.symm)]

end GlobalTheory.ZJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowPointIntegralPadicGroupScheme
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology Filter GlobalTheory.Points

namespace GlobalTheory.IntegralPower

theorem eventually_extends {V C : Type} [CommRing V] [IsLocalRing V] [CommRing C] [TopologicalSpace C]
    (σ : V →+* C) (hσ : Function.Injective σ) (ho : IsOpen (Set.range σ)) {X : Scheme.{0}} (q : X ⟶ Sp V)
    [LocallyOfFiniteType q] (y : Sp V ⟶ X) :
    ∀ᶠ x : Sp C ⟶ X in 𝓝 (spMap σ ≫ y), x ≫ q = spMap σ →
      ∃ z : Sp V ⟶ X, z ≫ q = 𝟙 _ ∧ spMap σ ≫ z = x := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_le y (le_preimage_top _)
  have hy' : ⊤ ≤ (spMap σ ≫ y) ⁻¹ᵁ U := le_preimage_comp _ y hy (le_preimage_top _)
  let c : V →+* Γ(X, U) := (q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  have hc : ∀ a, c a = constFn q U a := fun _ => rfl
  have hft : c.FiniteType := (q.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2)
  letI := c.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType V Γ(X, U) from hft).out
  have h1 : ∀ᶠ x : Sp C ⟶ X in 𝓝 (spMap σ ≫ y), ∀ f ∈ s, valR x U f ∈ Set.range σ := by
    refine (eventually_all_finset s).2 fun f _ => (continuousAt_valR f hy').eventually (ho.mem_nhds ?_)
    exact ⟨_, (valR_spMap_comp σ y U hy f).symm⟩
  filter_upwards [h1, (isOpen_setOf_le_preimage U).mem_nhds hy'] with x hx hxU hxq
  have h2 : ∀ f, (valMap x U hxU).hom f ∈ σ.range := by
    intro f
    have hf : f ∈ Algebra.adjoin V (s : Set Γ(X, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      rw [← valR_eq]
      exact hx f hf
    | algebraMap a =>
      rw [← valR_eq]
      exact ⟨a, (valR_constFn_of_over q σ x hxq U hxU a).symm⟩
    | add f g _ _ hf hg =>
      rw [map_add]
      exact add_mem hf hg
    | mul f g _ _ hf hg =>
      rw [map_mul]
      exact mul_mem hf hg
  let e : V ≃+* σ.range := RingEquiv.ofBijective σ.rangeRestrict
    ⟨fun a b h => hσ (congrArg Subtype.val h), σ.rangeRestrict_surjective⟩
  let ψ : Γ(X, U) →+* V := e.symm.toRingHom.comp ((valMap x U hxU).hom.codRestrict σ.range h2)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom σ = valMap x U hxU := by
    ext f
    exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h2 f⟩)
  have hz : spMap σ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec = x := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, specMap_valMap_fromSpec]
  refine ⟨_, ?_, hz⟩
  rw [← hz, Category.assoc] at hxq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ≫ q)
  rw [← hφ, ← Spec.map_comp] at hxq
  rw [← hφ, ← Spec.map_id]
  congr 1
  ext a
  exact hσ (congrArg (fun u => u.hom a) (Spec.map_injective hxq))

section Group

variable {C : Type} [CommRing C] [TopologicalSpace C] {S : Scheme.{0}} (t : Sp C ⟶ S)

omit [TopologicalSpace C] in

abbrev leftPt {A : Over S} (x : Over.mk t ⟶ A) : Sp C ⟶ A.left := x.left

abbrev ptTopology (A : Over S) : TopologicalSpace (Over.mk t ⟶ A) :=
  TopologicalSpace.induced (leftPt t) (topology C A.left)

attribute [local instance] ptTopology

theorem isEmbedding_leftPt (A : Over S) : IsEmbedding (leftPt t (A := A)) :=
  ⟨⟨rfl⟩, fun _ _ h => Over.OverMorphism.ext h⟩

theorem compactSpace_of_ptsOver (A : Over S) [CompactSpace (PtsOver A.hom t)] :
    CompactSpace (Over.mk t ⟶ A) :=
  Function.Surjective.compactSpace (f := fun x : PtsOver A.hom t => (Over.homMk x.1 x.2 : Over.mk t ⟶ A))
    ((isEmbedding_leftPt t A).continuous_iff.2 continuous_subtype_val) fun x => ⟨⟨x.left, Over.w x⟩, rfl⟩

theorem continuous_comp_over {A B : Over S} (g : A ⟶ B) : Continuous fun x : Over.mk t ⟶ A => x ≫ g :=
  (isEmbedding_leftPt t B).continuous_iff.2 ((continuous_comp g.left).comp (isEmbedding_leftPt t A).continuous)

variable [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]

theorem continuous_lift (A B : Over S) :
    Continuous fun q : (Over.mk t ⟶ A) × (Over.mk t ⟶ B) => lift q.1 q.2 := by
  refine (isEmbedding_leftPt t _).continuous_iff.2 ?_
  refine (isEmbedding_of_isPullback (C := C) (IsPullback.of_hasPullback A.hom B.hom)).continuous_iff.2 ?_
  refine ((isEmbedding_leftPt t A).continuous.prodMap (isEmbedding_leftPt t B).continuous).congr fun q => ?_
  exact Prod.ext (congrArg (·.left) (lift_fst q.1 q.2)).symm (congrArg (·.left) (lift_snd q.1 q.2)).symm

theorem isTopologicalGroup (G : Over S) [GrpObj G] : IsTopologicalGroup (Over.mk t ⟶ G) where
  continuous_mul := (continuous_comp_over t (μ[G])).comp (continuous_lift t G G)
  continuous_inv := continuous_comp_over t (GrpObj.inv (X := G))

end Group

attribute [local instance] ptTopology in

theorem exists_pow_extends {V F : Type} [CommRing V] [IsLocalRing V] [NormedField F] [ProperSpace F]
    (σ : V →+* F) (hσ : Function.Injective σ) (ho : IsOpen (Set.range σ)) (G : Over (Sp V)) [GrpObj G]
    [LocallyOfFiniteType G.hom] (h : IsProjOver (pullback.snd G.hom (spMap σ))) (a : Over.mk (spMap σ) ⟶ G) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp V)) ⟶ G, toUnit _ ≫ g = a ^ k := by
  have h1 : CompactSpace (Pts (pullback.snd G.hom (spMap σ))) := PtsOver.compactSpace h _
  have h2 := (PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback G.hom (spMap σ))).compactSpace
  have h3 := compactSpace_of_ptsOver (spMap σ) G
  have h4 := isTopologicalGroup (spMap σ) G
  let r : (𝟙_ (Over (Sp V)) ⟶ G) →* (Over.mk (spMap σ) ⟶ G) :=
    MonoidHom.mk' (fun g => toUnit _ ≫ g) fun g g' => comp_mul _ g g'
  have hr : ∀ g, leftPt _ (r g) = spMap σ ≫ g.left := fun g => by
    have : (toUnit (Over.mk (spMap σ))).left = spMap σ := (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap σ))))
    exact congrArg (· ≫ g.left) this
  have hopen : IsOpen (r.range : Set (Over.mk (spMap σ) ⟶ G)) := by
    refine r.range.isOpen_of_mem_nhds (g := r 1) ?_
    have h5 := eventually_extends σ hσ ho G.hom (1 : 𝟙_ (Over (Sp V)) ⟶ G).left
    rw [← hr] at h5
    filter_upwards [(isEmbedding_leftPt _ G).continuous.continuousAt.eventually h5] with x hx
    obtain ⟨z, hz, hzx⟩ := hx (Over.w x)
    exact ⟨Over.homMk z hz, (isEmbedding_leftPt _ G).injective ((hr _).trans hzx)⟩
  have h6 : Finite (_ ⧸ r.range) := r.range.quotient_finite_of_isOpen hopen
  obtain ⟨k, hk, -, g, hg⟩ := r.range.exists_pow_mem_of_index_ne_zero Subgroup.index_ne_zero_of_finite a
  exact ⟨k, hk, g, hg⟩

theorem exists_pow_integral : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] [LocallyOfFiniteType G.hom] [IsSeparated G.hom], IsProjOver (pullback.snd G.hom (spMap (algebraMap (integralClosure ℤ_[p] K) K))) → ∀ a : Over.mk (spMap (algebraMap (integralClosure ℤ_[p] K) K)) ⟶ G, ∃ k : ℕ, 1 ≤ k ∧ ∃ g : 𝟙_ (Over (Sp (integralClosure ℤ_[p] K))) ⟶ G, toUnit _ ≫ g = a ^ k := by
  intro p _ K _ G _ _ _ h a
  letI : NormedField K := inferInstanceAs (NormedField K.toSubfield)
  letI : NormedSpace ℚ_[p] K := ⟨fun c x => norm_smul_le c (x : PadicAlgCl p)⟩
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  haveI : IsUltrametricDist K := ⟨fun x y z => IsUltrametricDist.dist_triangle_max (x : PadicAlgCl p) y z⟩
  refine exists_pow_extends _ Subtype.val_injective ?_ G h a
  convert IsUltrametricDist.isOpen_closedBall (0 : K) one_ne_zero using 1
  ext x
  rw [mem_closedBall_zero_iff]
  exact (Set.ext_iff.1 Subtype.range_val x).trans (mem_integralClosure_padicInt_iff K x)

end GlobalTheory.IntegralPower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusExtensionDescentGaloisInvariant
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem exists_splitExt_of_galois_invariant :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  intro k K _ _ _ _ _ G₀ B₀ _ _ _ hB₀ G B _ _ X _ _ _ φG φ hG hB q i hq hfl hsu hqc hi H hinv
  have hc := GlobalTheory.ZM.DwModel.isGaloisCover_field k K
  let s : (K ≃ₐ[k] K) → (G.left ⟶ G.left) := fun τ =>
    hG.1.lift φG (G.hom ≫ spMap (τ : K →+* K)) (by rw [Category.assoc, hc.inv, hG.1.w])
  have hs₁ : ∀ τ, s τ ≫ φG = φG := fun τ => hG.1.lift_fst _ _ _
  have hs₂ : ∀ τ, s τ ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) := fun τ => hG.1.lift_snd _ _ _
  have hcG := hc.of_isPullback (ρ' := s) hG.1.flip hs₂ hs₁
  have hT := SplitTorus.isPullback_bcMap (spMap (algebraMap k K)) X
  have hcT := hc.of_isPullback
    (ρ' := fun τ : K ≃ₐ[k] K => SplitTorus.bcMap (spMap (τ : K →+* K)) X) hT.flip
    (fun τ => SplitTorus.bcMap_hom _ X) (fun τ => pullback.hom_ext
      (by
        have e := SplitTorus.bcMap_torusFst (spMap (algebraMap k K)) X
        exact (Category.assoc _ _ _).trans ((congrArg _ e).trans
          ((SplitTorus.bcMap_torusFst _ X).trans e.symm)))
      (by
        have e := SplitTorus.bcMap_hom (spMap (algebraMap k K)) X
        refine (Category.assoc _ _ _).trans ((congrArg _ e).trans (Eq.trans ?_ e.symm))
        rw [SplitTorus.bcMap_hom_assoc, hc.inv]))
  obtain ⟨q', hq', -⟩ := hcG.existsUnique_desc (q.left ≫ φ) fun τ => (hinv τ _ (hs₁ τ) (hs₂ τ)).1
  obtain ⟨i', hi', -⟩ := hcT.existsUnique_desc (i.left ≫ φG) fun τ => by
    rw [← Category.assoc, (hinv τ _ (hs₁ τ) (hs₂ τ)).2, Category.assoc, hs₁]
  have wq : q' ≫ B₀.hom = G₀.hom :=
    (hcG.existsUnique_desc (φG ≫ G₀.hom) fun τ => by rw [← Category.assoc, hs₁]).unique
      (by rw [← Category.assoc, hq', Category.assoc, hB.1.w, ← Category.assoc, Over.w, hG.1.w]) rfl
  have wi : i' ≫ G₀.hom = (splitTorus (Sp k) X).hom :=
    (hcT.existsUnique_desc (SplitTorus.bcMap (spMap (algebraMap k K)) X ≫ (splitTorus (Sp k) X).hom)
      fun τ => by rw [← Category.assoc, hcT.inv]).unique
      (by rw [← Category.assoc, hi', Category.assoc, hG.1.w, ← Category.assoc, Over.w, hT.w]) rfl
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := splitTorus_extension_descends k K (algebraMap k K) G B G₀ B₀ X
    φG φ hG hB q i (Over.homMk q' wq) (Over.homMk i' wi) hq' hi' hq hfl hsu hqc hi H
  obtain ⟨O, a, b, c, h⟩ := exists_gtDatum_of_splitTorus_extension (Sp k) X G₀ B₀ hB₀ _ _
    h₁ h₅ h₂ h₃ h₄ h₆
  obtain ⟨d, -⟩ := h hB₀
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroLocusSpecialFibreIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecialFibreLocus

theorem exists_sec_nonzeroLocus_iff : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (IsLocalRing.maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), ∃ θ : LB.Sec D.toPre.P.L, ∀ y : (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, (fstG (IsLocalRing.maximalIdeal V) 0 G).left y ∈ nonzeroLocus ϑ ↔ (U.gt 0).pG.left y ∈ nonzeroLocus θ := by
  intro hG V _ _ _ D A G _ _ U ϑ
  obtain ⟨f, hf⟩ := GlobalTheory.FewZeros.exists_weight_zero hG U ϑ
  obtain ⟨s, hs⟩ := GlobalTheory.FewZeros.exists_sec_of_formEq_id D.toPre.P.isLB (fun U _ k => by
    have e : toUnit D.toPre.P.A ≫ D.toPre.c 0 = 1 := cPoint_zero (D := D.toPre) _
    have e₁ : padd D.toPre.P.A (𝟙 D.toPre.P.A) 1 = 𝟙 D.toPre.P.A := _root_.mul_one (𝟙 D.toPre.P.A)
    have e₂ : toUnit D.toPre.P.A ≫ η[D.toPre.P.A] = 1 := rfl
    simp [Out.DegPre.famφB, Out.DegPre.famε, Fin.prod_univ_four, e, e₁, e₂]) f
  exact ⟨s, fun y => hs ▸ hf y⟩

end GlobalTheory.SpecialFibreLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusActionWeightedChartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_action_weighted_charts : Out.Laws → Out.Laws2 → ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F F' : J → (Φ.H 1).Sec) (π : Φ.Pol N) (m : Matrix J J k) (Ch : GlobalTheory.ZJ.Charts Φ.G.left) (e : Ch.I ≃ J) (cl : Φ.E.X → Ch.Cl), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → IsUnit m.det → (∀ i, IsLin Φ.G.hom F (m i) (F' i)) → (∀ α β, cl α = cl β ↔ ∃ n, α = β + N • n) → cl 0 = Ch.c₀ → (∀ i j, m (e i) j ≠ 0 → Ch.wt i = cl (cls j)) → (∀ i, Ch.W i = nonzeroLocus (F' (e i.1)) ∧ ∀ j, IsRatio (F' (e j)) (F' (e i.1)) (Ch.W i) (Ch.r i j)) → ∃ c : Fin (Module.finrank ℤ Φ.E.X) → Ch.Cl, GlobalTheory.ZJ.Charts.Split (H := Φ.G) Ch c := by
  first | exact @GlobalTheory.ZH.FibTorus.exists_split | exact GlobalTheory.ZH.FibTorus.exists_split | (intros; apply GlobalTheory.ZH.FibTorus.exists_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwoGoodSectionsNearClosedPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionTheory_om_of_tests_torsionSections : Semi.extend_existsSt.{0} → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), C.HasTests → T.BTest L → C.TorsSec n → T.Few n → L.CompanionTheory (T.Om L) := by
  first | exact @GlobalTheory.ZJ.Core.Law.six_of_few | exact GlobalTheory.ZJ.Core.Law.six_of_few | (intros; apply GlobalTheory.ZJ.Core.Law.six_of_few <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormVanishesOfTorsionTorusExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_vanishes_of_torsion_torusExtension : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ v, Crd (Φ.H 1) F x.left v ∧ MvPolynomial.eval v Pf = 0) → ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, MvPolynomial.eval v Pf = 0) := by
  first | exact @GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion | exact GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion | (intros; apply GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion <;> assumption)
end

