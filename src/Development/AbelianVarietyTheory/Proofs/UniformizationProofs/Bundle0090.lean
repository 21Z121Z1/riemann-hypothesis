import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0085
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.UniformizationBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MapUniq

variable {X X' : Scheme.{0}}

theorem hom_ext_of_gs {I : Type} (D : I → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (φ ψ : X' ⟶ X) (hm : ∀ i z, φ z ∈ D i → ψ z ∈ D i)
    (h : ∀ i z, φ z ∈ D i → ∀ a : Γ(X, D i), gs φ z _ a = gs ψ z _ a) : φ = ψ := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ z ∈ ⨆ i, D i by rw [hc]; trivial)
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ (φ ⁻¹ᵁ D i : Set X') from hi) (φ ⁻¹ᵁ D i).isOpen
  have e₁ : V ≤ φ ⁻¹ᵁ D i := hle
  have e₂ : V ≤ ψ ⁻¹ᵁ D i := fun y hy => hm i y (e₁ hy)
  have e : φ.appLE (D i) V e₁ = ψ.appLE (D i) V e₂ := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => fn_ext fun y hy => ?_)
    have k : ∀ (χ : X' ⟶ X) (e : V ≤ χ ⁻¹ᵁ D i), gs (𝟙 X') y V ((χ.appLE (D i) V e).hom a) = gs χ y _ a :=
      fun χ e => ((gs_res (𝟙 X') y e hy _).trans (gs_pull (𝟙 X') χ y _ (e hy) a)).trans (by rw [Category.id_comp])
    rw [k, k]
    exact h i y (e₁ hy) a
  refine ⟨V, hzV, ?_⟩
  have hV' : IsAffineOpen V := hV
  rw [← cancel_epi hV'.isoSpec.inv, ← Category.assoc, ← Category.assoc, hV'.isoSpec_inv_ι,
    ← (hD i).SpecMap_appLE_fromSpec φ hV' e₁, ← (hD i).SpecMap_appLE_fromSpec ψ hV' e₂, e]

theorem gs_cst {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (W : X.Opens)
    (h : φ z ∈ W) (c : R) :
    gs φ z W (AbLaw.cst f W c) = gs (φ ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  (gs_res φ z le_top h _).trans (gs_pull φ f z ⊤ trivial _)

theorem hom_eq_of_pull_sections : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ ψ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)) (w' : LB.Iso H' (H.pull ψ)), H'.IsLB → φ ≫ f = ψ ≫ f → w.IsGen → w'.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (ψ) z ∈ (H).U k → z ∈ (H').U k' → gs (ψ) z _ ((s j).f k) = (Geo.Tor.gw (w') (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → φ = ψ := by
  intro R _ X f H n s hH hs X' H' s' φ ψ w w' hH' hf _ _ hφ hψ
  choose r hr hsurj using fun i => (hs.2 i).2
  have mem : ∀ (χ : X' ⟶ X) (u : LB.Iso H' (H.pull χ)),
      (∀ j z (k : H.ι) (k' : H'.ι), χ z ∈ H.U k → z ∈ H'.U k' →
        gs χ z _ ((s j).f k) = (Geo.Tor.gw u (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k')) →
      ∀ i z k', z ∈ H'.U k' → (χ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs (𝟙 X') z _ ((s' i).f k'))) ∧
        (χ z ∈ nonzeroLocus (s i) → ∀ j, gs (𝟙 X') z _ ((s' j).f k') =
          gs χ z _ (r i j) * gs (𝟙 X') z _ ((s' i).f k')) := by
    intro χ u hu i z k' hk'
    obtain ⟨k, hk⟩ := exists_chart hH (χ z)
    refine ⟨?_, fun hz j => ?_⟩
    · rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) χ z hk, hu i z k k' hk hk', Units.isUnit_units_mul]
    · have e := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) χ z hz hk
      rw [hu i z k k' hk hk', hu j z k k' hk hk', mul_left_comm] at e
      exact (Units.mul_right_inj _).1 e
  have hm : ∀ i z, φ z ∈ nonzeroLocus (s i) → ψ z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact (mem ψ w' hψ i z k' hk').1.2 ((mem φ w hφ i z k' hk').1.1 hz)
  refine hom_ext_of_gs (fun i => nonzeroLocus (s i)) (fun i => (hs.2 i).1) hs.1 φ ψ hm fun i z hz a => ?_
  obtain ⟨k', hk'⟩ := exists_chart hH' z
  have hz' := hm i z hz
  have hrr : ∀ j, gs φ z _ (r i j) = gs ψ z _ (r i j) := fun j =>
    ((mem φ w hφ i z k' hk').1.1 hz).mul_right_cancel
      (((mem φ w hφ i z k' hk').2 hz j).symm.trans ((mem ψ w' hψ i z k' hk').2 hz' j))
  obtain ⟨p, rfl⟩ := hsurj i a
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, gs_cst f φ z _ hz, gs_cst f ψ z _ hz', hf]
  | add p q hp hq => rw [map_add, gs_add φ z _ hz, gs_add ψ z _ hz', hp, hq]
  | mul_X p j hp => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul φ z _ hz, gs_mul ψ z _ hz', hp, hrr]

end GlobalTheory.MapUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPowerStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.relAmple_externalTensorPower_groupPower : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → RelAmple G L → RelAmple G' (boxLB L p.pr) := by
  first | exact @GlobalTheory.relAmple_boxLB | exact GlobalTheory.relAmple_boxLB | (intros; apply GlobalTheory.relAmple_boxLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem relAmple_of_veryAmpleBy {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
    {L : LB A.left} (hL : L.IsLB) {N : ℕ} (hN : 1 ≤ N) {M : ℕ} (s : Fin (M + 1) → LB.Sec (pw L N))
    (hA : VeryAmpleBy A.hom (pw L N) s) : RelAmple A L := by
  intro U hU
  obtain ⟨hcov, hs⟩ := hA
  let ψ := (A.hom ⁻¹ᵁ U).ι
  have H : IsPullback ψ (A.hom ∣_ U) A.hom U.ι := (isPullback_morphismRestrict A.hom U).flip
  have : IsAffine U := hU
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := isLB_pw hL N
  have hP' := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have h₀ : LBIso (LB.LinComb L (K := Fin N) (fun _ => 𝟙 A.left) (fun _ => 1)) (pw L N) :=
    LBIso.chartPull (chartPullId _) (chartPullPw L N)
      ⟨_, idIso_isGen (linComb_isLB L hL (K := Fin N) (fun _ => 𝟙 A.left) (fun _ => 1))⟩
  obtain ⟨W, hW⟩ := LBIso.chartPull
    (chartPullSame L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 𝟙 A.left) (fun _ => 1) ψ
      fun _ => (Category.comp_id _).symm) (chartPullPull (pw L N) ψ ψ rfl) h₀
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A L U N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1
        ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (pw L N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A L U N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((U.ι.appLE ⊤ ⊤ le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      have e : ((A.hom ∣_ U).appLE ⊤ (nonzeroLocus (M := powOver A L U N) (s' i)) le_top).hom.comp
          ((U.ι.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) =
          (ψ.appLE _ _ (loc i).le).hom.comp (cst A.hom (nonzeroLocus (s i))) := by
        ext x
        exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) po.w.symm
      exact (congrArg (fun q => MvPolynomial.eval₂Hom q _ p) e).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

theorem relAmple_iff_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), L.IsLB → (RelAmple B L ↔ ∃ d : ℕ, 1 ≤ d ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (pw L d)), VeryAmpleBy B.hom (pw L d) s) := by
  intro R _ B L hL
  refine ⟨fun h => ?_, fun ⟨d, hd, n, s, hs⟩ => relAmple_of_veryAmpleBy hL hd s hs⟩
  obtain ⟨d, hd, n, s, -, hs⟩ := veryAmpleBy_of_relAmple hL h (𝟙 _) (Category.id_comp _) hL
    (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _) (𝟙 _) rfl) ⟨_, idIso_isGen hL⟩)
  exact ⟨d, hd, n, s, hs⟩

end GlobalTheory.Unif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.CubicalPackage

theorem surjective_appTop_of_injective {X S P S' : Scheme.{0}} {p : X ⟶ S} {q : P ⟶ S'} {d : P ⟶ X} {f : S' ⟶ S}
    (w : d ≫ p = q ≫ f) {e : S ⟶ X} {e' : S' ⟶ P} (he' : e' ≫ q = 𝟙 _) (hee : e' ≫ d = f ≫ e)
    (hd : Function.Injective d.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective p.appTop.hom := by
  intro a
  obtain ⟨b, hb⟩ := hq (d.appTop.hom a)
  have c : ∀ {A B C : Scheme.{0}} (g : A ⟶ B) (h : B ⟶ C) (x : Γ(C, ⊤)),
      g.appTop.hom (h.appTop.hom x) = (g ≫ h).appTop.hom x := fun g h x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  refine ⟨e.appTop.hom a, hd ?_⟩
  rw [c, w, ← c, c f e, ← hee, ← c, ← hb, c e' q, he', Scheme.Hom.id_appTop]
  rfl

variable {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {A : Over (Spec (CommRingCat.of K))} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem surjective_cube_of_generic [Flat G.hom] (gp : IsGrpPullback A G (etaK V K) F)
    (h : Function.Surjective (G3 A).hom.appTop.hom) : Function.Surjective (G3 G).hom.appTop.hom := by
  have hp := gp.1
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd (G3 G).hom (etaK V K))
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
  have hx : ∀ i, (x i).left ≫ F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
  let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
  have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have hl : l.left ≫ (cubeMapOf gp).F3 = pullback.fst (G3 G).hom (etaK V K) := hom_ext_triple _ fun i => by
    rw [Category.assoc, f3, ← Category.assoc, ← Over.comp_left, lx, hx]
  have inj : Function.Injective (l.left ≫ (cubeMapOf gp).F3).appTop.hom := by
    rw [hl]
    exact Exist.CubicalExtension.app_injective_generic (IsPullback.of_hasPullback _ _) ⊤
  refine surjective_appTop_of_injective (d := (cubeMapOf gp).F3) (f := etaK V K)
    (Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2)))))
    (e := eSec (G3 G)) (e' := eSec (G3 A)) (Over.w η[G3 A]) ?_ ?_ h
  · rw [CubeExtension.eSec_three, CubeExtension.eSec_three]
    refine hom_ext_triple _ fun i => ?_
    have a : ∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B],
        (lift (1 : 𝟙_ (Over S) ⟶ B) (lift (1 : 𝟙_ (Over S) ⟶ B) (1 : 𝟙_ (Over S) ⟶ B))).left ≫ (x3 B i).left =
          eSec B := fun B _ _ => by
      rw [← Over.comp_left, eSec]
      fin_cases i <;> simp [x3, Hom.one_def]
    rw [Category.assoc, f3, ← Category.assoc, a, Category.assoc, a]
    exact (cubeMapOf gp).e_comm
  · rw [Scheme.Hom.comp_appTop] at inj
    exact Function.Injective.of_comp (f := l.left.appTop.hom) inj

theorem exists_package : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G), LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → ∃ P : CP G, P.L = L) := by
  intro laws V _ _ _ hV A G _ _ hG eA hA L h₁
  have := hV.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := A.isAb.comm
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK V) (eA.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  have hi : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨w, hw⟩ : LBIso A.L (L.L.pull (eA.inv.left ≫ pullback.fst G.hom (jK V))) :=
    LBIso.chartPull (chartPullSec A.L _ eA.inv.left hi) (chartPullSame L.L _ _ _ eA.inv.left fun _ => rfl) h₁
  obtain ⟨c⟩ := (laws.cube _ A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  obtain ⟨c'⟩ := PolExtension.nonempty_cubical laws.cubicalExtends gp L c w hw
  obtain ⟨s, hs, hs'⟩ := PolExtension.exists_symmetry gp L.isLB A.isLB A.sym w hw
  exact ⟨CP.ofSurjective (surjective_cube_of_generic gp (surjective_cube laws.globalFns A.isAb)) L c' s hs hs', rfl⟩

end GlobalTheory.CubicalPackage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (gs_eq r z _ (hJ.mem φ r) _).trans ?_
  exact (congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → ∀ (s : U.SecK k) (F : Fam D.toPre (FractionRing R) k), (∀ jj, s.f jj = 0) → U.Expands k s F → F = 0 := by
  intro R _ _ I D A G _ _ U k hR s F hs hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  obtain ⟨r, hr, σ, f, h₁, hf, hE⟩ := hE
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hσ : ∀ j, σ.f j = 0 := fun j => by
    refine ExpInt.generic_app_injective G _ (Eq.trans (fn_ext fun y hy => ?_) (map_zero _).symm)
    obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB y
      (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
    have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left) = j a := fun a => by
      rw [Subsingleton.elim a 0]; exact e ()
    have e₂ := ExpInt.secScal_sval h₁ (𝟙 _) y hJ
    rw [sval_eq_zero hs _ y hJ, mul_zero, sval_of σ _ y J j ej] at e₂
    refine ((gs_pull (𝟙 _) _ y _ hy _).trans e₂).trans ((gs_eq _ y _ hy _).trans ?_).symm
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have hf0 : ∀ α j, (f α).f j = 0 := fun α => by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ f (fun j => ?_) (hE e) α j)
    exact (congrArg _ (hσ j)).trans (map_zero _)
  refine fam_ext fun α j => ?_
  refine sec_ext_val D.toPre.P.isLB (s' := SecOps.secZero) (fun y J hJ => ?_) j
  have e₁ := ExpInt.secScal_sval (hf α) (𝟙 _) y hJ
  rw [sval_eq_zero (hf0 α) _ y hJ, ExpInt.gs_scal] at e₁
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing R)).hom =
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
  rw [e₃] at e₁
  refine Eq.trans ?_ (sval_eq_zero (fun _ => rfl) _ y hJ).symm
  exact (IsUnit.mul_right_eq_zero (ExpInt.isUnit_cst _ y hr)).1 e₁.symm

end GlobalTheory.ExpZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPowersExpansionSupportSubgroupStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPowers_expansion_support_subgroup : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  first | exact @GlobalTheory.UU.exists_pow_exp_supp | exact GlobalTheory.UU.exists_pow_exp_supp | (intros; apply GlobalTheory.UU.exists_pow_exp_supp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPullSubsingleton
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifPullCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange (CarriesFam GrpPull RigPull UnifPull GenericInPsiLocus UnifBaseChange)
open GlobalTheory.PullDegCompare
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Bundle

end Bundle

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']

omit [IsDomain R] [IsDomain R'] in
theorem isGrpPullback_of_bc (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) :
    IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
  ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl

def toGrpPull (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) : GrpPull φ G G' where
  F := bc.hom.left ≫ pullback.fst G.hom (specOf φ)
  cart := (isGrpPullback_of_bc bc hbc).1
  F_one := PolBaseChange.eSec_comm (isGrpPullback_of_bc bc hbc)
  F_mul := (isGrpPullback_iff (isGrpPullback_of_bc bc hbc).1).1 (isGrpPullback_of_bc bc hbc)

omit [IsDomain R] [IsDomain R'] in
theorem exists_toGrpPull_eq (p : GrpPull φ G G') :
    ∃ (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom), toGrpPull bc hbc = p := by
  obtain ⟨e, me, he⟩ := grpPullback_iso ((isGrpPullback_iff p.cart).2 p.F_mul)
    (isGrpPullback_pullback G (specOf φ))
  obtain ⟨F, cart, F₁, Fm⟩ := p
  dsimp only at he
  subst he
  exact ⟨e, me, rfl⟩

def grpPullEquiv (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] :
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G // IsMonHom bc.hom} ≃ GrpPull φ G G' :=
  Equiv.ofBijective (fun b => toGrpPull b.1 b.2)
    ⟨fun b b' H => Subtype.ext (Iso.ext (Over.OverMorphism.ext (pullback.hom_ext (congrArg GrpPull.F H)
      ((Over.w b.1.hom).trans (Over.w b'.1.hom).symm)))),
     fun p => let ⟨bc, hbc, e⟩ := exists_toGrpPull_eq p; ⟨⟨bc, hbc⟩, e⟩⟩

variable [IsCommMonObj G] [IsCommMonObj G']

def rigPullEquiv (p : GrpPull φ G G') (L : RigLB G) (L' : RigLB G') :
    {w : LB.Iso L'.L (L.L.pull p.F) // w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
        (rigPullOf p.F (specOf φ) p.F_one L.L L.rig)} ≃ RigPull p L L' where
  toFun w := ⟨w.1, w.2.1, (rig_iff _ _ p.F_one _ _ w.1 L.rig L'.rig).1 w.2.2⟩
  invFun r := ⟨r.w, r.w_gen, (rig_iff _ _ p.F_one _ _ r.w L.rig L'.rig).2 r.w_rig⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {I : Ideal R} {I' : Ideal R'}

variable {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}

end Main

end GlobalTheory.UnifPullCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPointsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisedArc_iso_matches_levelPoints : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  first | exact @GlobalTheory.ArcLevel.level_match | exact GlobalTheory.ArcLevel.level_match | (intros; apply GlobalTheory.ArcLevel.level_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.weilQkIs_iff_commutatorPairing_torsion : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x x', QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F k p' x' → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs A.A A.L k x x' (unitOn ζ) := by
  first | exact @GlobalTheory.UT.weilQkIs_iff_weilIs | exact GlobalTheory.UT.weilQkIs_iff_weilIs | (intros; apply GlobalTheory.UT.weilQkIs_iff_weilIs <;> assumption)
end

