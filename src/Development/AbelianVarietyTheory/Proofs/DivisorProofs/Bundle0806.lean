import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0783
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarSpecialUnitaryProductChartFormula
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerExpJointHarmPos

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.MinSecond

section Transport

variable {p q : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isHW_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : IsHW a μ v) : IsHW b μ (e v) := by
  obtain ⟨h0, h1⟩ := hv
  refine ⟨fun h' => h0 (e.map_eq_zero_iff.mp h'), ?_⟩
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 ⊢
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← h, ← map_smul, ← map_sub, h1.1 i, map_zero]
  · rw [← h, h1.2 i j hij, map_zero]

theorem symm_equivariant (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v)) (Z : Mat p q) (w : W) :
    e.symm (b Z w) = a Z (e.symm w) := by
  apply e.injective
  rw [h, e.apply_symm_apply, e.apply_symm_apply]

theorem ofType_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : OfType a μ v) : OfType b μ (e v) := by
  obtain ⟨U, hf, hvU, hst, hw⟩ := hv
  refine ⟨U.map (e : V →ₗ[ℂ] W), inferInstance, ⟨v, hvU, rfl⟩, ?_, ?_⟩
  · rintro X hX _ ⟨u, hu, rfl⟩
    exact ⟨a X u, hst X hX u hu, h X u⟩
  · rintro ν _ ⟨u, hu, rfl⟩ hν
    refine hw ν u hu ?_
    have := isHW_equiv e.symm b a (symm_equivariant e a b h) ν _ hν
    simpa using this

theorem genSub_map (e : V →ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (S : Set V) (T : Set W) (hST : ∀ v ∈ S, e v ∈ T) (v : V) (hv : v ∈ genSub a S) :
    e v ∈ genSub b T := by
  simp only [genSub, Submodule.mem_sInf, Set.mem_ofPred_eq] at hv ⊢
  intro N hN
  refine hv (N.comap e) ⟨fun x hx => hN.1 (hST x hx), fun Z y hy => ?_⟩
  rw [Submodule.mem_comap, h]
  exact hN.2 Z _ hy

end Transport

noncomputable def swapPol (p q r s : ℕ) : Pol p q r s ≃ₗ[ℂ] Pol r s p q :=
  (renameEquiv ℂ (Equiv.prodComm (Ix p q) (Ix r s))).toLinearEquiv

end GlobalTheory.FockAlg.MinSecond

open GlobalTheory.FockAlg.MinSecond in

theorem GlobalTheory.FockAlg.min_second : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M2 → AdmGK M2 → Intw M1 M2 f → f ≠ 0 → ∀ (μ' : Ix r s → ℚ), (∃ v, IsHW M2.act μ' v) → (∀ ν w, IsHW M2.act ν w → degW (cPair p q) μ' ≤ degW (cPair p q) ν) → (∃ (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct2 p q r s) μ' P → f P ∈ Submodule.map f (genSub (fockAct1 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}) := by
  intro p q r s M1 M2 f hirr hadm hf hf0 μ' hμ hmin
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.fock_dualPair_swap_symmetry r s p q
  set e := swapPol r s p q with he
  have h1 : ∀ Z v, e (fockAct1 r s p q Z v) = fockAct2 p q r s Z (e v) := s1
  have h2 : ∀ Z v, e (fockAct2 r s p q Z v) = fockAct1 p q r s Z (e v) := s2
  have hJ : ∀ P, P ∈ jointHarm r s p q → e P ∈ jointHarm p q r s := fun P hP =>
    ⟨(s3 P).1.mp hP.2, (s3 P).2.mp hP.1⟩
  set c := TensorProduct.comm ℂ M1.V M2.V with hc
  let g : Pol r s p q →ₗ[ℂ] TensorProduct ℂ M2.V M1.V :=
    (c : _ →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e : _ →ₗ[ℂ] _)
  have hg : ∀ P, g P = c (f (e P)) := fun _ => rfl
  have hcm : ∀ (A : Module.End ℂ M1.V) (B : Module.End ℂ M2.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hgI : Intw M2 M1 g := by
    refine ⟨fun X => LinearMap.ext fun P => ?_, fun X => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h1, this, hcm]
    · have := LinearMap.congr_fun (hf.1 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h2, this, hcm]
  have hg0 : g ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun P => ?_
    have := LinearMap.congr_fun h (e.symm P)
    rw [hg, e.apply_symm_apply, LinearMap.zero_apply] at this
    exact c.map_eq_zero_iff.mp this
  obtain ⟨⟨μ, P, hP, hP1, hP2, hP0⟩, hB⟩ := GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub r s p q M2 M1 g hirr hadm hgI hg0 μ' hμ hmin
  refine ⟨⟨μ, e P, hJ P hP, isHW_equiv e _ _ h2 _ _ hP2, isHW_equiv e _ _ h1 _ _ hP1, ?_⟩, ?_⟩
  · intro h
    apply hP0
    rw [hg, h, map_zero]
  · intro R hR
    obtain ⟨Q, hQ, hQe⟩ := hB (e.symm R)
      (ofType_equiv e.symm _ _ (symm_equivariant e _ _ h1) _ _ hR)
    refine ⟨e Q, ?_, ?_⟩
    · exact genSub_map e.toLinearMap (fockAct2 r s p q) (fockAct1 p q r s) h2 _
        {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}
        (fun v hv => ⟨hJ v hv.1, ofType_equiv e _ _ h1 _ _ hv.2⟩) Q hQ
    · rw [hg, hg, e.apply_symm_apply] at hQe
      exact c.injective hQe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueWit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EndLoc.HomGlue

theorem pmap_hom_ext {S Z Y : Scheme.{0}} (A : Over S) (𝒰 : Z.OpenCover) (t : Z ⟶ S)
    {g₁ g₂ : pullback A.hom t ⟶ Y} (h : ∀ i, pmap A t (𝒰.f i) ≫ g₁ = pmap A t (𝒰.f i) ≫ g₂) : g₁ = g₂ := by
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.snd A.hom t)) _ _ fun (i : 𝒰.I₀) => ?_
  have w : (pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t) ≫ A.hom =
      pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ 𝒰.f i ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
  have e : pullback.fst (pullback.snd A.hom t) (𝒰.f i) = pullback.lift _ _ w ≫ pmap A t (𝒰.f i) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.condition]
  show pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ g₁ = pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ g₂
  rw [e, Category.assoc, Category.assoc, h]

theorem over_hom_ext_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {X Y : Over Z} {g₁ g₂ : X ⟶ Y}
    (h : ∀ i, (Over.pullback (𝒰.f i)).map g₁ = (Over.pullback (𝒰.f i)).map g₂) : g₁ = g₂ := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ X.hom) _ _ fun (i : 𝒰.I₀) => ?_
  have e1 : ((Over.pullback (𝒰.f i)).map g₁).left ≫ pullback.fst Y.hom (𝒰.f i) =
      pullback.fst X.hom (𝒰.f i) ≫ g₁.left := pullback.lift_fst _ _ _
  have e2 : ((Over.pullback (𝒰.f i)).map g₂).left ≫ pullback.fst Y.hom (𝒰.f i) =
      pullback.fst X.hom (𝒰.f i) ≫ g₂.left := pullback.lift_fst _ _ _
  show pullback.fst X.hom (𝒰.f i) ≫ g₁.left = pullback.fst X.hom (𝒰.f i) ≫ g₂.left
  rw [← e1, ← e2, h i]

theorem isMonHom_of_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {G H : Over Z} [MonObj G] [MonObj H] (f : G ⟶ H)
    (hf : ∀ i, IsMonHom ((Over.pullback (𝒰.f i)).map f)) : IsMonHom f := by
  constructor
  · refine over_hom_ext_cover 𝒰 fun i => ?_
    have h := (hf i).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · refine over_hom_ext_cover 𝒰 fun i => ?_
    have h := (hf i).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]

theorem lbIso_pull_pull {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Y' ⟶ Y) :
    LBIso ((L.pull a).pull b) (L.pull (b ≫ a)) :=
  LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b) (fun _ => b ≫ a) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _))

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

theorem wit_w {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} (g : Z' ⟶ Z)
    (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f)) :
    pmap A t g ≫ f ≫ B.hom = pmap A t g ≫ pullback.snd A.hom t ≫ t := by
  obtain ⟨A', B', _, _, φA, φB, Φ, hA, hB, -, -, e, e1, e2, e3⟩ := h
  haveI : IsIso e := by
    have : e = hA.1.isoPullback.hom :=
      pullback.hom_ext (by rw [e1, IsPullback.isoPullback_hom_fst]) (by rw [e2, IsPullback.isoPullback_hom_snd])
    rw [this]
    infer_instance
  rw [← cancel_epi e]
  calc e ≫ pmap A t g ≫ f ≫ B.hom = (e ≫ pmap A t g ≫ f) ≫ B.hom := by simp only [Category.assoc]
    _ = A'.hom ≫ g ≫ t := by rw [e3, Category.assoc, hB.1.w, Over.w_assoc]
    _ = e ≫ pmap A t g ≫ pullback.snd A.hom t ≫ t := by
        rw [pullback.lift_snd_assoc, Category.assoc, reassoc_of% e2]

theorem isMonHom_pull_of_wit {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} (g : Z' ⟶ Z)
    (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f)) (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B)
    (hΦ : Φ.left ≫ pullback.fst B.hom t = f) : IsMonHom ((Over.pullback g).map Φ) := by
  obtain ⟨A', B', _, _, φA, φB, Φ', hA, hB, hΦ', -, e, e1, e2, e3⟩ := h
  have hPA := (isGrpPullback_pullback ((Over.pullback t).obj A) g).comp (isGrpPullback_pullback A t)
  have hPB := (isGrpPullback_pullback ((Over.pullback t).obj B) g).comp (isGrpPullback_pullback B t)
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hPA hA
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hB hPB
  have key : a.hom.left ≫ e ≫ pmap A t g = pullback.fst _ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, e1, ha']
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, reassoc_of% e2, Over.w_assoc a.hom]
      exact pullback.condition.symm
  have hmap : ((Over.pullback g).map Φ).left ≫ pullback.fst _ g = pullback.fst _ g ≫ Φ.left :=
    pullback.lift_fst _ _ _
  have eq : (Over.pullback g).map Φ = a.hom ≫ Φ' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply hPB.1.hom_ext
    · have lhs : ((Over.pullback g).map Φ).left ≫ pullback.fst _ g ≫ pullback.fst B.hom t =
          pullback.fst _ g ≫ f := by
        rw [← Category.assoc, hmap, Category.assoc, hΦ]
      have rhs : (a.hom ≫ Φ' ≫ b.hom).left ≫ pullback.fst _ g ≫ pullback.fst B.hom t =
          pullback.fst _ g ≫ f := by
        simp only [Over.comp_left, Category.assoc]
        rw [hb', ← e3, ← key]
        simp only [Category.assoc]
      exact lhs.trans rhs.symm
    · exact (Over.w _).trans (Over.w _).symm
  rw [eq]
  infer_instance

theorem local_iso (hL : L.IsLB) (hM : M.IsLB) {Z Z' : Scheme.{0}} {t : Z ⟶ S} {f : pullback A.hom t ⟶ B.left}
    (g : Z' ⟶ Z) [IsOpenImmersion g] (h : Wit A B L M (g ≫ t) (pmap A t g ≫ f))
    (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B) (hΦ : Φ.left ≫ pullback.fst B.hom t = f) :
    LBIso ((L.pull (pullback.fst A.hom t)).pull (((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange).ι)
      (((M.pull (pullback.fst B.hom t)).pull Φ.left).pull
        (((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange).ι) := by
  obtain ⟨A', B', _, _, φA, φB, Φ', hA, hB, -, hI, e, e1, e2, e3⟩ := h
  set U := ((Over.pullback t).obj A).hom ⁻¹ᵁ g.opensRange with hU
  have hr : Set.range ⇑(U.ι ≫ pullback.snd A.hom t) ⊆ Set.range ⇑g := by
    rintro _ ⟨x, rfl⟩
    have hx : U.ι x ∈ (U : Set _) := Scheme.Opens.range_ι U ▸ ⟨x, rfl⟩
    exact Scheme.Hom.mem_opensRange.1 hx
  have hl : IsOpenImmersion.lift g _ hr ≫ g = U.ι ≫ pullback.snd A.hom t := IsOpenImmersion.lift_fac _ _ _
  have wl : (U.ι ≫ pullback.fst A.hom t) ≫ A.hom = IsOpenImmersion.lift g _ hr ≫ g ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ t) hl.symm).trans (Category.assoc _ _ _)
  have he' : pullback.lift _ _ wl ≫ pmap A t g = U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hl]
  have he : hA.1.isoPullback.inv ≫ e = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, e1, IsPullback.isoPullback_inv_fst, Category.id_comp]
    · rw [Category.assoc, e2, IsPullback.isoPullback_inv_snd, Category.id_comp]
  obtain ⟨E, hE⟩ : ∃ E, E ≫ e = pullback.lift _ _ wl :=
    ⟨pullback.lift _ _ wl ≫ hA.1.isoPullback.inv, by rw [Category.assoc, he, Category.comp_id]⟩
  have h2 : LBIso (L.pull (U.ι ≫ pullback.fst A.hom t)) ((M.pull (pullback.fst B.hom t)).pull (U.ι ≫ Φ.left)) := by
    refine lbIso_pull hL hM E ?_ ?_ hI
    · rw [← e1, ← Category.assoc, hE, pullback.lift_fst]
    · rw [Category.assoc, hΦ, ← e3, ← Category.assoc, hE, ← Category.assoc, he']
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
    (lbIso_pull_pull hL _ _) (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _)
      (pull_isLB (pull_isLB (pull_isLB hM _) _) _) h2 (lbIso_pull_pull (pull_isLB hM _) _ _).symm)

theorem glue_wit : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), (∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f)) → HomGlue.Wit A B L M t f := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 t f hw
  have w : f ≫ B.hom = pullback.snd A.hom t ≫ t :=
    pmap_hom_ext A 𝒰 t fun i => wit_w (𝒰.f i) (hw i)
  let Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B :=
    Over.homMk (pullback.lift f (pullback.snd A.hom t) w) (pullback.lift_snd _ _ _)
  have hΦf : Φ.left ≫ pullback.fst B.hom t = f := pullback.lift_fst _ _ _
  have hΦ : IsMonHom Φ := isMonHom_of_cover 𝒰 Φ fun i => isMonHom_pull_of_wit (𝒰.f i) (hw i) Φ hΦf
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj t B hB
  haveI : IsCommMonObj ((Over.pullback t).obj A) := hA'.comm
  haveI : IsCommMonObj ((Over.pullback t).obj B) := hB'.comm
  have hI : LBIso (L.pull (pullback.fst A.hom t)) ((M.pull (pullback.fst B.hom t)).pull Φ.left) :=
    hiso Z _ _ _ _ Φ hΦ hA' hB' (pull_isLB hL _) (pull_isLB hM _)
      (GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback A t) hrA)
      (GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback B t) hrB)
      fun z => ⟨(𝒰.f (𝒰.idx z)).opensRange, Scheme.Hom.mem_opensRange.2 (𝒰.covers z),
        local_iso hL hM (𝒰.f (𝒰.idx z)) (hw _) Φ hΦf⟩
  exact ⟨_, _, inferInstance, inferInstance, _, _, Φ, isGrpPullback_pullback A t, isGrpPullback_pullback B t, hΦ,
    hI, 𝟙 _, Category.id_comp _, Category.id_comp _, (Category.id_comp _).trans hΦf.symm⟩

end GlobalTheory.EndLoc.HomGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParam
section
noncomputable section

namespace GlobalTheory.ParamLabel

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.GLq GlobalTheory.GoodCharsCompare GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {p : ℕ} [Fact p.Prime]

theorem isCusp_psi (θ : Fbar p →* ℂ) (hθ : ∀ x y : Fbar p, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) {d k : ℕ} (hd : 0 < d)
    (hk : ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card (ZMod p) ^ i ≡ k [MOD Nat.card (ZMod p) ^ d - 1]) :
    IsCusp (fun x : Gn p d => (-1) ^ (d - 1) *
      psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p)))) := by
  classical
  obtain ⟨hch, hip⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular (ZMod p) θ hθ d k hd hk
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod p) θ k).1
  refine ⟨hd, ?_, fun a ha had => ?_⟩
  · have hs := GlobalTheory.T.star_virtualCharacter_eq_apply_inv _ _ (AddSubgroup.subset_closure (k := {χ | BI.IsChar ℂ ℂ χ}) hch)
    obtain ⟨n, ρ, hρ⟩ := hch
    have hρ' : ∀ x, (FDRep.of ρ).character x = (-1) ^ (d - 1) *
      psi (rootSum θ k) (Fin d → ZMod p) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod p))) :=
      fun x => (hρ x).symm
    refine ⟨FDRep.of ρ, ?_, hρ'⟩
    rw [FDRep.simple_iff_char_is_norm_one]
    rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties (ZMod p) d (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype, glCard] at hip
    rw [← hip]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : ((-1 : ℂ) ^ (d - 1)) * ((-1 : ℂ) ^ (d - 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [hρ', hρ', ← hs x, star_mul', star_pow, star_neg, star_one, mul_mul_mul_comm, h1, one_mul]
  · have h := GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive (ZMod p) d _ (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse (ZMod p) (Fin d → ZMod p) _ hadd) a ha had
    rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
    have h2 := congrArg (fun z : ℂ => (-1 : ℂ) ^ (d - 1) * z) h
    simp only [mul_zero, Finset.mul_sum] at h2
    unfold res
    refine mul_eq_zero_of_right _ (Eq.trans ?_ h2)
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ (Formalism.D.Classical.grUnipBlock d a : Set (GL (Fin d) (ZMod p)))
    · rw [if_pos ((GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).1 hu), Set.indicator_of_mem (by exact hu)]
    · rw [if_neg (mt (GlobalTheory.GreenExists.mem_grUnipBlock_iff had u).2 hu), Set.indicator_of_notMem (by exact hu), mul_zero]

theorem thetaOf_gen (L : LabelDatum p) {d : ℕ} (hd : 0 < d) (k : ℕ) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    thetaOf L d (L.gen d ^ k) z = L.teich z ^ k := by
  have hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  haveI : NeZero (p ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨n, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hz
  rw [Model.thetaOf_gen_pow L hd (by rw [← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]),
    ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem torVal_eq {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) (F : Fbar p → ℂ)
    (h : ∀ u : Tor p d, ((θ u : ℂˣ) : ℂ) = F ((u : (Fbar p)ˣ) : Fbar p)) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    torVal θ z = F z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (g_pow_sub_pos hd).ne'] at hz
    exact zero_ne_one hz
  let u : Tor p d := ⟨Units.mk0 z hz0, (mem_rootsOfUnity _ _).2 (Units.ext (by simpa using hz))⟩
  have hinj : Function.Injective (fun u : Tor p d => ((u : (Fbar p)ˣ) : Fbar p)) :=
    fun a b e => Subtype.ext (Units.ext e)
  exact (hinj.extend_apply (fun u => ((θ u : ℂˣ) : ℂ)) 0 u).trans (h u)

theorem cuspOn_eq_psi {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 0 < Fintype.card ι) {ω : Fbar p →*₀ ℂ}
    (hω : Function.Injective ω) (θ : Tor p (Fintype.card ι) →* ℂˣ) (k : ℕ)
    (h : ∀ u : Tor p (Fintype.card ι), ((θ u : ℂˣ) : ℂ) = ω ((u : (Fbar p)ˣ) : Fbar p) ^ k) :
    cuspOn θ = fun y : Gn p (Fintype.card ι) => (-1) ^ (Fintype.card ι - 1) *
      psi (rootSum (ω : Fbar p →* ℂ) k) (Fin (Fintype.card ι) → ZMod p) (Matrix.toLin' y.val) := by
  classical
  funext y
  obtain ⟨x, hx, hx'⟩ := exists_preimage hω hd (z := rootC (p ^ Fintype.card ι - 1) ^ k)
    (by rw [← pow_mul, mul_comm, pow_mul, (rootC_prim (g := p) hd).pow_eq_one, one_pow])
  have hM : (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self]
    exact y.det_ne_zero
  have e1 : cuspOn θ y = cuspVal ω x (y.val.submatrix (Fintype.equivFin ι) (Fintype.equivFin ι)) := by
    unfold cuspOn cuspChar cuspVal
    split_ifs with hh
    · obtain ⟨q, m, hq, hm⟩ := hh
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz1 := root_pow hM hq hm (y := z) (Multiset.mem_toFinset.1 hz)
      obtain ⟨a, ha⟩ := exists_log ω hd hz1
      rw [torVal_eq hd θ (fun z => ω z ^ k) h hz1, labelChar_eq ω hd hx ha, hx', ha, ← pow_mul, ← pow_mul,
        mul_comm a k]
      rfl
    · rfl
  rw [e1, GlobalTheory.CuspFormula.cuspVal_eq_psi ω hd hx hx' _ hM,
    ← GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj _ _ _ _ (LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (Fintype.equivFin ι)) (Matrix.toLin' y.val)]
  congr 2
  refine LinearMap.ext fun v => ?_
  show Matrix.toLin' (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm y.val) v = _
  rw [Matrix.toLin'_reindex]
  rfl

theorem isCuspOf_cuspOn (L : LabelDatum p) {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p) (hd : 0 < Fintype.card ι) (hL : LabelsChar L θ x)
    (hx : (minpoly (ZMod p) x).natDegree = Fintype.card ι) : IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) := by
  classical
  obtain ⟨hx1, hθ⟩ := hL
  have hp : IsPrimitiveRoot (L.gen (Fintype.card ι)) (p ^ Fintype.card ι - 1) :=
    L.gen_order _ hd ▸ IsPrimitiveRoot.orderOf _
  haveI : NeZero (p ^ Fintype.card ι - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  obtain ⟨k, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx1
  obtain ⟨ω, hω, he⟩ := exists_ext (ι := Units.map L.teich) fun a b e =>
    Units.ext (L.teich_inj _ _ a.ne_zero b.ne_zero (congrArg Units.val e))
  have he' : ∀ z : Fbar p, z ^ (p ^ Fintype.card ι - 1) = 1 → L.teich z = ω z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (g_pow_sub_pos hd).ne'] at hz
      exact zero_ne_one hz
    exact he (Units.mk0 z hz0)
  have e := cuspOn_eq_psi hd hω θ k fun u => by
    have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ Fintype.card ι - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
    rw [hθ, thetaOf_gen L hd k hu, he' _ hu]
  have hc : Nat.card (ZMod p) = p := Nat.card_zmod p
  refine ⟨⟨minpoly.monic (isInt _), minpoly.irreducible (isInt _),
    minpoly.coeff_zero_ne_zero (isInt _) (pow_ne_zero _ (hp.ne_zero (g_pow_sub_pos hd).ne')), hx⟩, ?_, ?_⟩
  · rw [e]
    exact isCusp_psi _ (fun _ _ _ _ h => hω h) hd
      (GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow (ZMod p) _ k (L.gen _) hd (by rw [hc]; exact L.gen_order _ hd) hx)
  · intro x₀ hx₀ y hy z hz
    obtain ⟨j, rfl⟩ := mem_roots_minpoly.1 hx₀
    have hz1 := root_pow y.det_ne_zero hy (pow_one _).symm hz
    rw [Fintype.card_fin] at hz1
    have h := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible (ZMod p) _ _ (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow (ZMod p) (ω : Fbar p →* ℂ) k).1
      (Matrix.toLin' y.val) (by rw [Matrix.charpoly_toLin']; exact hy)
    rw [Matrix.charpoly_toLin'] at h
    rw [e]
    show _ * _ = _
    rw [h]
    congr 1
    change ((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _
    have hnd : y.val.charpoly.natDegree = Fintype.card ι := by simp
    rw [GlobalTheory.GreenExists.rootsBar_eq hy ((mem_rootsBar hy.ne_zero).1 hz), hnd, Multiset.map_map]
    have hs := sum_shift (g := p) (z := ω z) (m := k) (e := Fintype.card ι)
      (by rw [mul_comm, pow_mul, ← map_pow, pow_g_of hz1]) j
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hs.symm.trans (Finset.sum_congr rfl fun i _ => ?_))
    · simp only [Function.comp, MonoidHom.coe_coe, map_pow, ← pow_mul, mul_comm]
    · have hzi : (z ^ p ^ i) ^ (p ^ Fintype.card ι - 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
      rw [← pow_mul (L.gen _), thetaOf_gen L hd _ hzi, he' _ hzi, map_pow, ← pow_mul, ← pow_mul]
      congr 1
      ring

theorem isCuspOf_cuspOn_of_green : GlobalTheory.GLq.Green → ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p), 5 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p), 0 < Fintype.card ι → LabelsChar L θ x → (minpoly (ZMod p) x).natDegree = Fintype.card ι → GlobalTheory.GLq.IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) :=
  fun _ _ _ L _ _ _ _ θ x hd hL hx => isCuspOf_cuspOn L θ x hd hL hx

end GlobalTheory.ParamLabel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarSpecialUnitaryProductChartFormulaStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_specialUnitary_product_chart_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (ν : Measure (realSU X.Ψ X.Gm)) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), 1 ≤ r → IsOrth X x → ν.IsHaarMeasure → (∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x) → 0 < ρ → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ A : Set (ChartSp X), MeasurableSet A → A ⊆ Metric.ball 0 (min ρ Real.pi) → ν ((fun w : ChartSp X => σ w.1 * t w.2) '' A) = ∫⁻ w in A, ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ ((r - 1) * X.Ψ.card)) ∂(volume : Measure (ChartSp X)) := by
  first | exact @GlobalTheory.FibreVol.haar_chart_formula | exact GlobalTheory.FibreVol.haar_chart_formula | (intros; apply GlobalTheory.FibreVol.haar_chart_formula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimesLossLogSumAdmissible
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.InertLossAdm

theorem inertPrimes_loss_log_sum_admissible : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  intro eps Fm h0 h1
  obtain ⟨C1, x1, hC1, hc⟩ := GlobalTheory.ConjLossPrimes.loss_sum_primes Fm h0 h1
  obtain ⟨C2, x2, hC2, hi⟩ := GlobalTheory.OtherLoss.inertLoss_primeSum Fm h0 h1
  refine ⟨C1 + C2, max x1 x2, add_nonneg hC1 hC2, ?_⟩
  intro x hx hx1 i j hj P hP
  rw [← Finset.sum_filter_add_sum_filter_not P
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)]
  have A := hc x (le_trans (le_max_left _ _) hx) hx1 i j hj (P.filter
    (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.2⟩)
  have B := hi x (le_trans (le_max_right _ _) hx) hx1 i j hj (P.filter
    (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)))
    (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact ⟨(hP p hp.1).1, (hP p hp.1).2.1, (hP p hp.1).2.2, hp.2⟩)
  have eA : ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0),
      2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_pos hp.2]
  have eB : ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |Formalism.MainNotions.WeightDegreeSizes.EatCI (Fm.L x i) Fm.GK Fm.cX.err j p| =
      ∑ p ∈ P.filter (fun p => ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)),
      2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    unfold Formalism.MainNotions.WeightDegreeSizes.EatCI
    rw [if_neg hp.2]
  rw [eA, eB, add_mul]
  exact add_le_add A B

end GlobalTheory.InertLossAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerExpJointHarmPosStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_expt_jointHarm_real_pos : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Y ∈ pR p q, ∀ P ∈ jointHarm p q r s, P ≠ 0 → (inner ℂ (F.ι P) (F.π (T1.expt Y, 1) (F.ι P))).im = 0 ∧ 0 < (inner ℂ (F.ι P) (F.π (T1.expt Y, 1) (F.ι P))).re := by
  first | exact @GlobalTheory.HarmCoeff.inner_exp_jointHarm_pos | exact GlobalTheory.HarmCoeff.inner_exp_jointHarm_pos | (intros; apply GlobalTheory.HarmCoeff.inner_exp_jointHarm_pos <;> assumption)
end

