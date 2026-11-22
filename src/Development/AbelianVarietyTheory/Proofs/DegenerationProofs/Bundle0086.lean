import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueSectionsSameThetaMultiple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GlueTheta

theorem res_res {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem glue_secOn {X : Scheme.{0}} (L : LB X) {I : Type} (V : I → X.Opens) (W : X.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : ∀ x ∈ W, ∃ i, x ∈ V i) (σ : ∀ i j, Γ(X, V i ⊓ L.U j)) (hσ : ∀ i, σ i ∈ secOn L (V i))
    (hc : ∀ i i' j (O : X.Opens) (h : O ≤ V i ⊓ L.U j) (h' : O ≤ V i' ⊓ L.U j),
      resG X h (σ i j) = resG X h' (σ i' j)) :
    ∃ s ∈ secOn L W, ∀ i j, resG X (inf_le_inf_right _ (hle i)) (s j) = σ i j := by
  have key : ∀ j, ∃ s : Γ(X, W ⊓ L.U j), ∀ i, resG X (inf_le_inf_right _ (hle i)) s = σ i j := by
    intro j
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V i ⊓ L.U j) (W ⊓ L.U j)
      (fun i => homOfLE (inf_le_inf_right _ (hle i)))
      (fun x hx => by
        obtain ⟨i, hi⟩ := hcov x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi, hx.2⟩)
      (fun i => σ i j) (fun i i' => hc i i' j _ inf_le_left inf_le_right)
    exact ⟨s, hs⟩
  choose s hs using key
  refine ⟨s, fun j k => ?_, fun i j => hs j i⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => V i ⊓ L.U j ⊓ L.U k) (W ⊓ L.U j ⊓ L.U k)
    (fun i => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hle i))))
    (fun x hx => by
      obtain ⟨i, hi⟩ := hcov x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨hi, hx.1.2⟩, hx.2⟩) _ _ fun i => ?_
  have h := hσ i j k
  rw [← hs j i, ← hs k i, res_res, res_res] at h
  change resG X _ _ = resG X _ _
  rw [map_mul, res_res, res_res, res_res]
  exact h

theorem exists_glue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q c huniq W hloc
  choose N σ hz hNW hsec hth hne using fun z : W => hloc z.1 z.2
  obtain ⟨s, hs, hres⟩ := glue_secOn Q.LOne (fun z : W => Q.G.hom ⁻¹ᵁ N z) (Q.G.hom ⁻¹ᵁ W)
    (fun z x hx => hNW z hx) (fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩) σ hsec
    (fun z z' => huniq _ _ _ _ (hth z) (hth z'))
  have hval : ∀ (K : Type) [Field K] (g : Sp K ⟶ Q.G.left) (z : W) (j : Q.LOne.ι),
      ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) → valF g _ (σ z j) = valF g _ (s j) := by
    intro K _ g z j h
    rw [← hres z j]
    exact GlobalTheory.Points.valR_res g _ h _
  refine ⟨s, hs, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    let z : W := ⟨Q.G.hom ((g ≫ Q.φ) (IsLocalRing.closedPoint K)), h5 ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z) := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U fun _ => jL) := fun t ht =>
      ⟨hN ht, Set.mem_iInter.2 fun _ => h4 ⟨t, rfl⟩⟩
    rw [← hval K _ z _ hU]
    exact hth z K β g r jP jL h1 h2 h3 h4 (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
  · intro K _ _ x hx
    let z : W := ⟨x (IsLocalRing.closedPoint K), hx ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ x ⁻¹ᵁ N z := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    obtain ⟨g, j, hg, hv⟩ := hne z K x (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
    refine ⟨g, j, hg, ?_⟩
    have hU : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) := by
      by_contra hU
      exact hv (dif_neg hU)
    rwa [← hval K g z j hU]

end GlobalTheory.ZH.GlueTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateOfSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnitTheta

theorem exists_pull_one {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (θ : LB.Sec L) :
    ∃ th : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval th ρ z J = gs (ρ ≫ f) z _ (θ.f (J (ρ ≫ f))) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤ f ⁻¹ᵁ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  let u : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) := fun j =>
    (Y.presheaf.map (homOfLE (le j)).op).hom ((f.app _).hom (θ.f (j 0)))
  have hu : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) j, ρ z ∈ LB.wchart L (fun _ : Fin 1 => f) j →
      gs ρ z _ (u j) = gs (ρ ≫ f) z _ (θ.f (j 0)) := fun Z ρ z j h =>
    (gs_res ρ z _ h _).trans (gs_pull ρ f z _ (le j h) _)
  refine ⟨⟨u, fun j j' => fn_ext fun y hy => ?_⟩, fun Z ρ z J hJ => hu Z ρ z _ (hJ.mem (fun _ : Fin 1 => f) ρ)⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val
      (gm_linComb L (fun _ : Fin 1 => f) (fun _ => 1) (𝟙 Y) y j j' hy.1 hy.2))) (gs_res (𝟙 Y) y _ hy _))).symm)
  rw [Fin.prod_univ_one, zpow_one]
  exact (hu _ (𝟙 Y) y j hy.1).trans ((gs_compat θ (𝟙 Y ≫ f) y (le j hy.1) (le j' hy.2)).trans
    (congrArg (_ * ·) (hu _ (𝟙 Y) y j' hy.2).symm))

theorem exists_good_point_of_sec : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  intro hB hG S P θ κ _ _ r n hn hκ ⟨z, hz, p, hp⟩ b
  obtain ⟨th, hth⟩ := exists_pull_one P.L (snd (Over.mk r) P.A).left θ
  have hne : SecM.ofSec P.A (a := 1) (T := Over.mk r) th ≠ 0 := fun e => by
    obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback r P.A.hom) p z hp
    let y' : (Over.mk r ⊗ P.A).left := y
    obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB y' (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
    have h₁ : (𝟙 _ ≫ (snd (Over.mk r) P.A).left) y' ∈ nonzeroLocus θ := by
      rw [Category.id_comp]; exact hy ▸ hz
    have h₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ y' (hJ _)).1 h₁
    rw [← hth _ _ y' J hJ] at h₂
    have h₃ : th.f (fun _ => J (𝟙 _ ≫ (snd (Over.mk r) P.A).left)) = 0 :=
      congrArg (fun s : SecM P.A P.L 1 (Over.mk r) => s.1 _) e
    rw [sval, h₃] at h₂
    exact not_isUnit_zero ((congrArg IsUnit (GlobalTheory.UT.ExactTerm.gs_zero' _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk r) P.A).left) (𝟙 _)))).mp h₂)
  obtain ⟨x, hx, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hG hB P r hn hκ th hne b
  refine ⟨x, hx, fun q _ => ?_⟩
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h₁ : IsUnit (sval th (ptSecT P.A (b * x)).left q J) := hu q J hJ
  have e : (ptSecT P.A (b * x)).left ≫ (snd (Over.mk r) P.A).left = (b * x).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  rw [hth _ _ q J hJ, e] at h₁
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ q (hJ _)).2 h₁

end GlobalTheory.UnitTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomSpecOfLeRingOn
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem comp_opens_toSpecΓ_eq_valMap {C : Type} [CommRing C] {X : Scheme.{0}} (U : X.Opens)
    (eta : Sp C ⟶ U.toScheme) (h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U) :
    eta ≫ U.toSpecΓ = Spec.map (valMap (eta ≫ U.ι) U h) := by
  have e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  rw [← appLE_valMap eta U.ι e (le_preimage_top eta) h, Scheme.Opens.toSpecΓ, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Spec.map_comp, valMap, Spec.map_comp]
  have h1 : (Sp C).toSpecΓ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of C)).hom := by
    rw [← Scheme.isoSpec_Spec_hom]; rfl
  have h2 : U.topIso.inv = U.ι.appLE U ⊤ e := by
    rw [Scheme.Opens.ι_appLE]; rfl
  rw [h1, h2]
  rfl

theorem exists_hom_spec_of_le_ringOn :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  intro o Ω _ _ _ M U R hU hR
  let ψ : R →+* Γ(M.Z, U) :=
    (M.sectionsEquiv U hU).symm.toRingHom.comp (Subalgebra.inclusion hR).toRingHom
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), fun eta he => ?_⟩
  have h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U := he ▸ M.top_le_preimage_pt hU
  rw [← Category.assoc, comp_opens_toSpecΓ_eq_valMap U eta h, ← Spec.map_comp]
  congr 1
  ext a
  have e : (M.sectionsEquiv U hU (ψ a) : Ω) = a :=
    congrArg Subtype.val ((M.sectionsEquiv U hU).apply_symm_apply _)
  rw [coe_sectionsEquiv, ← he, valF_eq_valR, valR_eq _ U h] at e
  exact e

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatios
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem eq_of_res_eq_of_nonempty {U : M.Z.Opens} {f g : Γ(M.Z, U)}
    (h : ∀ hU : (U : Set M.Z).Nonempty, M.res U hU f = M.res U hU g) : f = g := by
  by_cases hU : (U : Set M.Z).Nonempty
  · exact M.res_injective U hU (h hU)
  · obtain rfl : U = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hU)
    exact Subsingleton.elim _ _

theorem exists_unit_res_eq {U : M.Z.Opens} {x : Ω} (hx : x ≠ 0) (h : ∀ z ∈ U, x ∈ M.O z)
    (h' : ∀ z ∈ U, x⁻¹ ∈ M.O z) :
    ∃ g : Γ(M.Z, U)ˣ, ∀ hU : (U : Set M.Z).Nonempty, M.res U hU (g : Γ(M.Z, U)) = x := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨a, ha⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h)
    obtain ⟨b, hb⟩ := (mem_ringOn_iff_exists hU).1 (mem_ringOn.2 h')
    have hab : a * b = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, res_apply, res_apply, ha, hb, mul_inv_cancel₀ hx])
    exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun _ => (M.res_apply U hU a).trans ha⟩
  · exact ⟨1, fun h => (hU h).elim⟩

theorem exists_isLB_genTriv_of_ratios : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  intro o Ω _ _ _ M ι U d hU hd hr
  have key : ∀ k k', ∃ g : Γ(M.Z, U k ⊓ U k')ˣ, ∀ h : ((U k ⊓ U k' : M.Z.Opens) : Set M.Z).Nonempty,
      M.res _ h (g : Γ(M.Z, U k ⊓ U k')) = d k' / d k := fun k k' =>
    M.exists_unit_res_eq (div_ne_zero (hd k') (hd k)) (hr k k') fun z hz => by
      rw [inv_div]
      exact hr k' k z ⟨hz.2, hz.1⟩
  choose g hg using key
  have hres : ∀ k k' {V : M.Z.Opens} (h : V ≤ U k ⊓ U k') (hV : (V : Set M.Z).Nonempty),
      M.res V hV ((Semi.res h (g k k') : Γ(M.Z, V)ˣ) : Γ(M.Z, V)) = d k' / d k := fun k k' V h hV =>
    (M.res_resG h hV _).trans (hg k k' _)
  refine ⟨g, ⟨hU, fun i => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_),
    fun i j k => Units.ext (M.eq_of_res_eq_of_nonempty fun hV => ?_)⟩,
    ⟨hd, fun k k' h => (M.res_apply _ h _).symm.trans (hg k k' h)⟩⟩
  · refine (hres i i _ hV).trans ?_
    rw [div_self (hd i), Units.val_one, map_one]
  · rw [Units.val_mul, map_mul]
    refine (congrArg₂ (· * ·) (hres i j _ hV) (hres j k _ hV)).trans (Eq.trans ?_ (hres i k _ hV).symm)
    have := hd i
    have := hd j
    field_simp

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullbackOfProjChart
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}

theorem IsHom.apply_genericPoint_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (h : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) : q (genericPoint N.Z) ∈ W := by
  rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
  have e : (N.pt ≫ q) (IsLocalRing.closedPoint Ω') =
      (spMap φ.toRingHom ≫ M.pt) (IsLocalRing.closedPoint Ω') := by
    rw [show N.pt ≫ q = _ from h]
  have e' : q (N.pt (IsLocalRing.closedPoint Ω')) = M.pt (spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) := e
  rw [e']
  exact M.top_le_preimage_pt hW (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial

theorem IsHom.comp_id {N Q : RatModel o Ω'} {q : N.Z ⟶ M.Z} {a : Q.Z ⟶ N.Z} (h : M.IsHom N φ q)
    (ha : N.IsHom Q (AlgHom.id o Ω') a) : M.IsHom Q φ (a ≫ q) := by
  simpa only [AlgHom.id_comp] using h.comp ha

theorem exists_isHom_of_projChart {N₁ N₂ : RatModel o Ω'} {q₁ : N₁.Z ⟶ M.Z} {q₂ : N₂.Z ⟶ M.Z}
    (h₁ : M.IsHom N₁ φ q₁) (h₂ : M.IsHom N₂ φ q₂) {J : Type} [Finite J] {t : J → Ω'}
    (h : ∀ z, ∃ (W : M.Z.Opens) (i : J), q₁ z ∈ W ∧ N₁.Div t i z ∧ M.ProjChart N₂ φ q₂ W t) :
    ∃ a, N₂.IsHom N₁ (AlgHom.id o Ω') a := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨W, i, hz, hi, hc⟩ := h z
  obtain ⟨U, hU, hD, hR⟩ := hc.2 i hi.1
  refine ⟨q₁ ⁻¹ᵁ W ⊓ ⟨_, N₁.isOpen_setOf_div t i⟩, U, ⟨hz, hi⟩, hU,
    ⟨genericPoint N₂.Z, hD ▸ ⟨h₂.apply_genericPoint_mem ⟨_, hz⟩, div_genericPoint hi.1⟩⟩,
    fun x hx => mem_ringOn.2 fun w hw => ?_⟩
  rw [hR] at hx
  refine (Algebra.adjoin_le ?_ : _ ≤ N₁.O w) hx
  rintro _ (⟨y, hy, rfl⟩ | ⟨j, rfl⟩)
  · exact h₁.map_mem_O (ringOn_le_O (M := M) (U := W) (z := q₁ w) hw.1 hy)
  · exact hw.2.2 j

theorem exists_isPullback_of_projChart_of_isPullback {N P Q : RatModel o Ω'} {U₀ : M.Z.Opens} {b : N.Z ⟶ U₀.toScheme}
    {f : P.Z ⟶ M.Z} {ι : Q.Z ⟶ P.Z} [IsOpenImmersion ι] {g : Q.Z ⟶ U₀.toScheme} (hι : P.IsHom Q (AlgHom.id o Ω') ι)
    (hpb : IsPullback ι g f U₀.ι) {J : Type} [Finite J] {t : J → Ω'} (hb : M.IsHom N φ (b ≫ U₀.ι))
    (hf : M.IsHom P φ f)
    (h : ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty →
      M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) :
    ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  have hU : ∀ {X : Scheme.{0}} (b : X ⟶ U₀.toScheme) (z : X), (b ≫ U₀.ι) z ∈ U₀ := fun b z => by
    rw [Scheme.Hom.comp_apply]
    exact (b z).2
  obtain ⟨a₀, ha₀⟩ : ∃ a, P.IsHom N (AlgHom.id o Ω') a := by
    refine exists_isHom_of_projChart hb hf (t := t) fun z => ?_
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (hU b z)
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h1.1 z hz
    exact ⟨W, i, hz, hi, h2⟩
  have hfι : M.IsHom Q φ (ι ≫ f) := hf.comp_id hι
  obtain ⟨c, hc⟩ : ∃ c, N.IsHom Q (AlgHom.id o Ω') c := by
    refine exists_isHom_of_projChart hfι hb (t := t) fun z => ?_
    have hz0 : (ι ≫ f) z ∈ U₀ := hpb.w ▸ hU g z
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hz0
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h2.1 (ι z) (by rwa [Scheme.Hom.comp_apply] at hz)
    refine ⟨W, i, hz, ⟨hi.1, fun j => ?_⟩, h1⟩
    rw [hι.O_eq z]
    exact hi.2 j
  have hw : a₀ ≫ f = b ≫ U₀.ι := IsHom.unique (φ := φ) (hf.comp_id ha₀) hb
  obtain ⟨a₁, e₁, e₂⟩ : ∃ a₁ : N.Z ⟶ Q.Z, a₁ ≫ ι = a₀ ∧ a₁ ≫ g = b :=
    ⟨hpb.lift a₀ b hw, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have ha₁ : Q.IsHom N (AlgHom.id o Ω') a₁ := by
    unfold IsHom at hι ha₀ ⊢
    have e : spMap (AlgHom.id o Ω').toRingHom = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp] at hι ha₀ ⊢
    rw [← cancel_mono ι, Category.assoc, e₁, hι, ha₀]
  have h₁ : a₁ ≫ c = 𝟙 N.Z := IsHom.unique (φ := AlgHom.id o Ω') (hc.comp_id ha₁) N.isHom_id
  have h₂ : c ≫ a₁ = 𝟙 Q.Z := IsHom.unique (φ := AlgHom.id o Ω') (ha₁.comp_id hc) Q.isHom_id
  have : IsIso a₁ := ⟨c, h₁, h₂⟩
  refine ⟨a₀, ha₀, ?_⟩
  exact hpb.of_iso (asIso a₁).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [← e₁]) (by simp [← e₂]) (by simp) (by simp)

theorem exists_isPullback_of_projChart :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  intro o Ω _ _ _ M Ω' _ _ φ _ N P U₀ b f J _ t hb hf h
  have hbU : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀ := by
    rw [Scheme.Hom.comp_apply]
    exact (b _).2
  have hV : ((f ⁻¹ᵁ U₀ : P.Z.Opens) : Set P.Z).Nonempty := ⟨_, hf.apply_genericPoint_mem ⟨_, hbU⟩⟩
  exact @exists_isPullback_of_projChart_of_isPullback o Ω _ _ _ M Ω' _ _ φ N P (P.openPart _ hV) U₀ b f
    (f ⁻¹ᵁ U₀).ι (inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ U₀).ι)) (f ∣_ U₀) (P.isHom_openPart _ hV)
    (isPullback_morphismRestrict f U₀).flip J _ t hb hf h

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LocThetaConv

variable {X Y : Scheme.{0}}

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem appLE_resG (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) {U : Y.Opens} (e : U ≤ f ⁻¹ᵁ W')
    (a : Γ(X, W)) : (f.appLE W' U e).hom (resG X h a) =
      (f.appLE W U (e.trans fun _ hy => h hy)).hom a := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem resG_appLE (f : Y ⟶ X) {W : X.Opens} {U U' : Y.Opens} (h : U' ≤ U) (e : U ≤ f ⁻¹ᵁ W)
    (a : Γ(X, W)) : resG Y h ((f.appLE W U e).hom a) = (f.appLE W U' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem g_val (L : LB X) {K : Type} [Fintype K] [Subsingleton K] (φ : K → (Y ⟶ X)) (k : K)
    (i j : K → L.ι) : ((LB.LinComb L φ (fun _ => 1)).g i j).val =
      ((φ k).appLE (L.U (i k) ⊓ L.U (j k)) (LB.wchart L φ i ⊓ LB.wchart L φ j)
        (le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))).hom
        (L.g (i k) (j k)).val := by
  simp only [LB.LinComb, zpow_one]
  erw [Fintype.prod_subsingleton _ k]
  rfl

theorem mem_one {L : LB X} {j : Fin 1 → L.ι} {x : X} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_pull' {L : LB X} (f : Y ⟶ X) {j : L.ι} {y : Y} :
    y ∈ (L.pull f).U (fun _ => j) ↔ f y ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_secOn (L : LB X) (V : X.Opens) (σ : LB.Sec (L.pull V.ι)) :
    ∃ τ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V,
      ∀ y ∈ nonzeroLocus σ, ∃ j, V.ι y ∈ X.basicOpen (τ j) := by
  set L₁ := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1) with hL₁
  have e : ∀ j : Fin 1 → L.ι, (L.pull V.ι).U (fun _ => j 0) ≤ V.ι ⁻¹ᵁ (V ⊓ L₁.U j) :=
    fun j y hy => ⟨y.2, mem_one.2 ((mem_pull' _).1 hy)⟩
  have e' : ∀ j : Fin 1 → L.ι, V.ι ⁻¹ᵁ (V ⊓ L₁.U j) ≤ (L.pull V.ι).U (fun _ => j 0) :=
    fun j y hy => (mem_pull' _).2 (mem_one.1 hy.2)
  have hV : V ≤ V.ι.opensRange := V.opensRange_ι.ge
  choose τ hτ using fun j : Fin 1 → L.ι =>
    (bijective_appLE V.ι _ (inf_le_left.trans hV) _ (e j) (e' j)).2 (σ.f fun _ => j 0)
  refine ⟨τ, fun i j => ?_, fun y hy => ?_⟩
  · apply (bijective_appLE V.ι (V ⊓ L₁.U i ⊓ L₁.U j) ((inf_le_left.trans inf_le_left).trans hV)
      ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
      (fun y hy => ⟨e i hy.1, (e j hy.2).2⟩) (fun y hy => ⟨e' i hy.1, e' j ⟨hy.1.1, hy.2⟩⟩)).1
    have h := σ.compat (fun _ => i 0) (fun _ => j 0)
    rw [← hτ i, ← hτ j] at h
    rw [map_mul]
    refine ((appLE_resG _ _ _ _).trans (resG_appLE _ _ _ _).symm).trans (h.trans ?_)
    congr 1
    · have h1 : ((L.pull V.ι).g (fun _ => i 0) (fun _ => j 0)).val =
          (V.ι.appLE (L.U (i 0) ⊓ L.U (j 0)) ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
            (fun y hy => ⟨(mem_pull' _).1 hy.1, (mem_pull' _).1 hy.2⟩)).hom
            (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : PUnit => V.ι) PUnit.unit _ _).trans (by rfl)
      have h2 : (L₁.g i j).val = resG X (fun y hy => ⟨mem_one.1 hy.1, mem_one.1 hy.2⟩ :
          L₁.U i ⊓ L₁.U j ≤ L.U (i 0) ⊓ L.U (j 0)) (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : Fin 1 => 𝟙 X) 0 _ _).trans (by rfl)
      rw [h1, h2]
      exact ((appLE_resG _ _ _ _).trans (appLE_resG _ _ _ _)).symm
    · exact (resG_appLE _ _ _ _).trans (appLE_resG _ _ _ _).symm
  · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    have h := Scheme.basicOpen_appLE V.ι _ _ (e fun _ => k PUnit.unit) (τ fun _ => k PUnit.unit)
    have h' := hτ fun _ => k PUnit.unit
    have hk' : y ∈ V.toScheme.basicOpen (σ.f fun _ => k PUnit.unit) := hk
    rw [← h'] at hk'
    exact (h.le hk').2

theorem exists_point {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

theorem exists_secFam_fibNe : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q H z
  obtain ⟨N, σ, hz, hσ⟩ := H z
  obtain ⟨τ, hτ, hne⟩ := exists_secOn Q.L.L _ σ
  refine ⟨N, τ, hz, hτ, fun K _ _ x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hσ _ (hx ⟨IsLocalRing.closedPoint K, rfl⟩)
  obtain ⟨j, hj⟩ := hne y hy
  have := Q.dim
  have : Smooth Q.G.hom := SmoothOfRelativeDimension.smooth S.g _
  obtain ⟨g, hg, hO⟩ := exists_point Q.G.hom x _ _ hj hyx
  exact ⟨g, j, hg, ((GlobalTheory.Points.le_preimage_basicOpen_iff g
    (GlobalTheory.Points.le_preimage_mono g (Scheme.basicOpen_le _ _) hO) (τ j)).1 hO).ne_zero⟩

end GlobalTheory.ZH.LocThetaConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrincipalPolarisationAbelianFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarisation_abelianFibre : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  first | exact @GlobalTheory.ZH.UFib.exists_pol | exact GlobalTheory.ZH.UFib.exists_pol | (intros; apply GlobalTheory.ZH.UFib.exists_pol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGeneratedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_lattice_twist_generated : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω), IsProjOver M.s → ∀ (J : Type) [Fintype J] (EE : M.Lat J), ∃ (n : ℕ) (t : Fin (n + 1) → Ω) (e m : ℕ) (v : Fin m → J → Ω), M.IsCl t ∧ ∀ z i, M.Div t i z → EE.E z = Submodule.span (M.O z) (Set.range fun k j => v k j / t i ^ e) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span | exact GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span | (intros; apply GlobalTheory.ZH.RatModel.exists_isCl_lat_eq_span <;> assumption)
end

