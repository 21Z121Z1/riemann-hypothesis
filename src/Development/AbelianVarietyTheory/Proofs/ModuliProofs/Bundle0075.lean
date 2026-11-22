import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSetOfHilbertFunctionsFibres
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}

theorem gs_one (x : X) (U : X.Opens) (h : x ∈ U) (f : Γ(X, U)) :
    gs (𝟙 X) x U f = (X.presheaf.germ U x h).hom f := by
  rw [gs_eq (𝟙 X) x U h]; rfl

theorem lbIso_of_germs (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → (∃ i, IsUnit (gs (𝟙 X) y (A.U k) ((a i).f k))) ∧
      ∃ u : (X.presheaf.stalk y)ˣ, ∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) :
    LBIso A B := by
  have uniq : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → ∀ u u' : (X.presheaf.stalk y)ˣ,
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) →
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u' * gs (𝟙 X) y (A.U k) ((a i).f k)) → u = u' := by
    intro y j k hj hk u u' h h'
    obtain ⟨i, hi⟩ := (H y j k hj hk).1
    exact Units.ext (hi.mul_right_cancel ((h i).symm.trans (h' i)))
  have loc : ∀ (j : B.ι) (k : A.ι) (y : ↥(B.U j ⊓ A.U k : X.Opens)), ∃ (W : X.Opens) (_ : W ≤ B.U j ⊓ A.U k) (c : Γ(X, W)ˣ),
      y.1 ∈ W ∧ ∀ z ∈ W, ∀ i, gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z W c * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    rintro j k ⟨y, hy⟩
    obtain ⟨⟨i₀, hi₀⟩, u, hu⟩ := H y j k hy.1 hy.2
    let t : Γ(X, B.U j ⊓ A.U k) := resG X inf_le_left ((b i₀).f j) * resG X inf_le_right ((a i₀).f k)
    have hle := X.basicOpen_le t
    have ht : IsUnit (resG X hle t) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace t
    rw [map_mul] at ht
    obtain ⟨c₁, h₁⟩ := isUnit_of_mul_isUnit_left ht
    obtain ⟨c₂, h₂⟩ := isUnit_of_mul_isUnit_right ht
    refine ⟨X.basicOpen t, hle, c₁ * c₂⁻¹, ?_, fun z hz i => ?_⟩
    · rw [X.mem_basicOpen t y hy, ← gs_one y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, hu]
      exact (u.isUnit.mul hi₀).mul hi₀
    · obtain ⟨-, u', hu'⟩ := H z j k (hle hz).1 (hle hz).2
      have e₁ : (gm (𝟙 X) z _ c₁).val = gs (𝟙 X) z (B.U j) ((b i₀).f j) := by
        rw [← gs_unit _ z _ hz, h₁, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e₂ : (gm (𝟙 X) z _ c₂).val = gs (𝟙 X) z (A.U k) ((a i₀).f k) := by
        rw [← gs_unit _ z _ hz, h₂, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e : gm (𝟙 X) z _ c₁ = u' * gm (𝟙 X) z _ c₂ := Units.ext (by rw [Units.val_mul, e₁, e₂, hu'])
      rw [map_mul, map_inv, e, mul_inv_cancel_right, hu']
  choose W hW c hy hc using loc
  have glue : ∀ (j : B.ι) (k : A.ι), ∃ w : Γ(X, B.U j ⊓ A.U k)ˣ, ∀ z ∈ B.U j ⊓ A.U k, ∀ i,
      gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z _ w * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    intro j k
    obtain ⟨w, hw⟩ := glue_unit (B.U j ⊓ A.U k) (W j k) (hW j k)
      (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hy j k ⟨z, hz⟩⟩) (c j k)
      (fun p q z hz => uniq z j k (hW j k p hz.1).1 (hW j k p hz.1).2 _ _ (hc j k p z hz.1) (hc j k q z hz.2))
    refine ⟨w, fun z hz i => ?_⟩
    rw [← gm_res (𝟙 X) z (hW j k ⟨z, hz⟩) (hy j k ⟨z, hz⟩), hw]
    exact hc j k ⟨z, hz⟩ z (hy j k ⟨z, hz⟩) i
  choose w hw using glue
  refine ⟨⟨fun p => w p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y p q hy)
    (gm_res _ y _ hy _))).symm)
  refine uniq y p.1 p.2 hy.1.1 hy.1.2 _ _ (hw p.1 p.2 y hy.1) fun i => ?_
  have hB : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
  have hA : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
  have eB := congrArg (gs (𝟙 X) y _) ((b i).compat p.1 q.1)
  have eA := congrArg (gs (𝟙 X) y _) ((a i).compat p.2 q.2)
  rw [gs_mul _ y _ hB, gs_res _ y _ hB, gs_res _ y _ hB, gs_unit _ y _ hB] at eB
  rw [gs_mul _ y _ hA, gs_res _ y _ hA, gs_res _ y _ hA, gs_unit _ y _ hA] at eA
  rw [eB, eA, hw q.1 q.2 y hy.2 i]
  change _ = ((_ * _ * gm (𝟙 X) y _ (w q.1 q.2) : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) * _
  rw [Units.val_mul, Units.val_mul]
  have := (gm (𝟙 X) y _ (A.g p.2 q.2)).inv_mul
  linear_combination (-(gm (𝟙 X) y _ (B.g p.1 q.1)).val * (gm (𝟙 X) y _ (w q.1 q.2)).val *
    gs (𝟙 X) y (A.U q.2) ((a i).f q.2)) * this

theorem coord_germ {M : LB X} {th : σ → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : σ → R}
    (h : SecCoord M th x v) (p : Sp R) (k : M.ι) (hk : x p ∈ M.U k) :
    ∃ t : ((Sp R).presheaf.stalk p)ˣ, ∀ i, gs x p (M.U k) ((th i).f k) =
      ((Sp R).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) * t := by
  obtain ⟨τ, -, h⟩ := h
  have hp : p ∈ (M.pull x).U (fun _ => k) := mem_pull.2 hk
  refine ⟨gm (𝟙 _) p _ (τ.s fun _ => k), fun i => ?_⟩
  have e := congrArg (gs (𝟙 _) p _) (h i (fun _ => k) (RepBC.pull_le M x _))
  rw [gs_appLE x _ _ _ (𝟙 _) p hp, gs_mul _ p _ hp, gs_res _ p _ hp, gs_one p ⊤ trivial, Category.id_comp] at e
  rw [← gs_unit _ p _ hp]
  exact e

theorem lbIso_of_coord (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ y : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : σ → R), IsOpenImmersion x ∧ y ∈ Set.range x ∧
      Ideal.span (Set.range v) = ⊤ ∧ SecCoord A a x v ∧ SecCoord B b x v) : LBIso A B := by
  refine lbIso_of_germs A B a b fun y j k hj hk => ?_
  obtain ⟨R, _, x, v, _, ⟨p, rfl⟩, hv, hA, hB⟩ := H y
  obtain ⟨t, ht⟩ := coord_germ hA p k hk
  obtain ⟨t', ht'⟩ := coord_germ hB p j hj
  let e := (asIso (x.stalkMap p)).commRingCatIsoToRingEquiv
  have he : ∀ (U : X.Opens) (_ : x p ∈ U) f, gs x p U f = e (gs (𝟙 X) (x p) U f) := fun U h f => gs_stalkMap x p U h f
  let ψ : R →+* (Sp R).presheaf.stalk p :=
    ((Sp R).presheaf.germ ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  constructor
  · have : ∃ i, IsUnit (ψ (v i)) := by
      by_contra hn
      push_neg at hn
      have : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal _).comap ψ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hn i
      rw [hv, top_le_iff, Ideal.comap_eq_top_iff] at this
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [← MulEquiv.isUnit_map e, ← he _ hk, ht]
    exact hi.mul t.isUnit
  · refine ⟨Units.map e.symm.toMonoidHom (t' * t⁻¹), fun i => e.injective ?_⟩
    rw [map_mul, ← he _ hk, ← he _ hj, ht, ht']
    have : e (Units.map e.symm.toMonoidHom (t' * t⁻¹)).val = (t' * t⁻¹).val := e.apply_symm_apply _
    rw [this, Units.val_mul]
    linear_combination (-(ψ (v i)) * t'.val) * t.inv_mul

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (a : Sp R' ⟶ Sp R) : ∃ φ : R →+* R', a = spMap φ :=
  ⟨(Spec.preimage a).hom, (Spec.map_preimage a).symm⟩

theorem exists_factor {U : Scheme.{0}} {R : Type} [CommRing R] (y : Sp R ⟶ X) (u : U ⟶ X) [IsOpenImmersion u]
    (p : Sp R) (h : y p ∈ Set.range u) : ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (a : Sp R' ⟶ U),
      IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ spMap φ ≫ y = a ≫ u := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := u) p q hq.symm
  obtain ⟨i, r, hr⟩ := (pullback y u).affineOpenCover.openCover.exists_eq z
  let C := (pullback y u).affineOpenCover.X i
  let w : Sp C ⟶ pullback y u := (pullback y u).affineOpenCover.f i
  have : IsOpenImmersion w := (pullback y u).affineOpenCover.map_prop i
  obtain ⟨φ, hφ⟩ := exists_spMap (w ≫ pullback.fst y u)
  refine ⟨C, inferInstance, φ, w ≫ pullback.snd y u, ?_, ?_, ?_⟩
  · rw [← hφ]; infer_instance
  · rw [← hφ]; refine ⟨r, ?_⟩
    rw [← hz, ← hr]; rfl
  · rw [← hφ, Category.assoc, Category.assoc, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
theorem exists_map_of_coord : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by
  intro R σ _ I Z Y s sY M N th ty ⟨hM, hloc, hpts⟩ hN hY
  have uniq : ∀ (T : Type) [CommRing T] (x x' : Sp T ⟶ Z) (v : σ → T), x ≫ s = x' ≫ s → SecCoord M th x v →
      SecCoord M th x' v → x = x' := by
    intro T _ x x' v e h h'
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
    obtain ⟨h₁, h₂⟩ := hloc T β x v hβ h
    exact (hpts T β v h₁ h₂).unique ⟨hβ, h⟩ ⟨e.symm.trans hβ, h'⟩
  have uni : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ → T), SecCoord N ty y v →
      Ideal.span (Set.range v) = ⊤ ∧ ∃ x : Sp T ⟶ Z, x ≫ s = y ≫ sY ∧ SecCoord M th x v := by
    intro T _ y v h
    obtain ⟨β, hβ⟩ := exists_spMap (y ≫ sY)
    obtain ⟨h₁, h₂⟩ := hY T β y v hβ h
    obtain ⟨x, hx, hx'⟩ := (hpts T β v h₁ h₂).exists
    exact ⟨h₁, x, hx.trans hβ.symm, hx'⟩
  choose A iA u v hu hp hv using (GlobalTheory.T.sectionCoordinateVector_exists_locally Y N σ ty hN).2.2
  choose g hg hgv using fun p => (uni (A p) (u p) (v p) (hv p)).2
  have key : ∀ (p : Y) (T : Type) [CommRing T] (a : Sp T ⟶ Sp (A p)), (∃ w, SecCoord N ty (a ≫ u p) w) ∧
      ∀ w, SecCoord N ty (a ≫ u p) w ↔ SecCoord M th (a ≫ g p) w := by
    intro p T _ a
    obtain ⟨φ, rfl⟩ := exists_spMap a
    have h₁ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN (hv p)).1 T φ
    have h₂ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM (hgv p)).1 T φ
    refine ⟨⟨_, h₁⟩, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨c, hc⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h₁).2.2 w h
      rw [show w = _ from funext hc]
      exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h₂).2.1 c
    · obtain ⟨c, hc⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h₂).2.2 w h
      rw [show w = _ from funext hc]
      exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h₁).2.1 c
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun p => Sp (A p)) u (fun p => ⟨p, hp p⟩) hu
  have hglue : ∀ p q : Y, pullback.fst (u p) (u q) ≫ g p = pullback.snd (u p) (u q) ≫ g q := by
    intro p q
    refine Scheme.Cover.hom_ext (pullback (u p) (u q)).affineOpenCover.openCover _ _ fun i => ?_
    let C := (pullback (u p) (u q)).affineOpenCover.X i
    let r : Sp C ⟶ pullback (u p) (u q) := (pullback (u p) (u q)).affineOpenCover.f i
    have e : (r ≫ pullback.fst _ _) ≫ u p = (r ≫ pullback.snd _ _) ≫ u q := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨⟨w, hw⟩, h⟩ := key p C (r ≫ pullback.fst _ _)
    have := uniq C _ _ w (by rw [Category.assoc, hg, ← Category.assoc, e, Category.assoc _ (g q), hg, Category.assoc _ (u q)])
      ((h w).1 hw) (((key q C (r ≫ pullback.snd _ _)).2 w).1 (e ▸ hw))
    rw [Category.assoc, Category.assoc] at this
    exact this
  let f : Y ⟶ Z := 𝒰.glueMorphisms g hglue
  have hf : ∀ p, u p ≫ f = g p := fun p => Scheme.Cover.ι_glueMorphisms 𝒰 _ hglue p
  have hfs : f ≫ s = sY := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change u p ≫ _ = u p ≫ _
    rw [← Category.assoc, hf, hg]
  refine ⟨f, hfs, ?_, fun T _ y w => ⟨fun h => ?_, fun h => ?_⟩, fun f' hf' h => ?_⟩
  · refine lbIso_of_coord N (M.pull f) ty (fun i => RepBC.secPull M f (th i)) fun p =>
      ⟨A p, iA p, u p, v p, hu p, hp p, (uni _ _ _ (hv p)).1, hv p, (RepBC.secCoord_pull M th f _ _).2 ?_⟩
    rw [hf]; exact hgv p
  · refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Z M σ th T _ w hM (uni T y w h).1 fun q => ?_
    have := hu (y q)
    obtain ⟨T', _, φ, a, h₁, h₂, e⟩ := exists_factor y (u (y q)) q (hp _)
    refine ⟨T', inferInstance, φ, h₁, h₂, ?_⟩
    rw [← Category.assoc, e, Category.assoc, hf, ← (key _ T' a).2, ← e]
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h).1 T' φ
  · obtain ⟨β, hβ⟩ := exists_spMap ((y ≫ f) ≫ s)
    refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Y N σ ty T _ w hN (hloc T β _ w hβ h).1 fun q => ?_
    have := hu (y q)
    obtain ⟨T', _, φ, a, h₁, h₂, e⟩ := exists_factor y (u (y q)) q (hp _)
    refine ⟨T', inferInstance, φ, h₁, h₂, ?_⟩
    rw [e, (key _ T' a).2, ← hf, ← Category.assoc, ← e, Category.assoc]
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h).1 T' φ
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change u p ≫ _ = u p ≫ _
    rw [hf]
    exact uniq _ _ _ (v p) (by rw [Category.assoc, hf', hg]) (h _ _ _ (hv p)) (hgv p)

end GlobalTheory.ZM.RepMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueFactorThroughEtaleIsogenyReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFactor

lemma ext_of_geometricPoints {T X Z : Scheme.{0}} [IsReduced T] (q : X ⟶ Z) [IsSeparated q]
    (f g : T ⟶ X) (h : f ≫ q = g ≫ q)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), x ≫ f = x ≫ g) : f = g := by
  classical

  let K : T → Type := fun t => AlgebraicClosure (T.residueField t)
  let pts : (∐ fun t : T => Sp (K t)) ⟶ T := Sigma.desc fun t =>
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) (K t))) ≫ T.fromSpecResidueField t

  have : Surjective pts := by
    refine ⟨fun t => ⟨Sigma.ι (fun t : T => Sp (K t)) t (IsLocalRing.closedPoint (K t)), ?_⟩⟩
    have e : (Sigma.ι (fun t : T => Sp (K t)) t ≫ pts) (IsLocalRing.closedPoint (K t)) = t := by
      simp only [pts, Sigma.ι_desc]
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e
  refine ext_of_isDominant_of_isSeparated q h pts ?_
  refine Sigma.hom_ext _ _ fun t => ?_
  simpa only [pts, Sigma.ι_desc_assoc] using H (K t) _

theorem exists_unique_factor : ∀ (S : Scheme.{0}) [IsReduced S] (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (ψ : A ⟶ B) (g : A ⟶ B'), IsAbelianScheme A → IsAbelianScheme B → IsSeparated B'.hom → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → IsMonHom g → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A), x ≫ ψ = 1 → x ≫ g = 1) → ∃ g' : B ⟶ B', IsMonHom g' ∧ ψ ≫ g' = g ∧ ∀ g'' : B ⟶ B', ψ ≫ g'' = g → g'' = g' := by
  intro S _ A B B' _ _ _ ψ g _ _ hsep hψ hfin het hsurj hg H

  let T : Over S := pullback ψ η[B]
  let i : T ⟶ A := pullback.fst ψ η[B]
  have hker : IsPullback i (toUnit T) ψ η[B] := by
    have hp := IsPullback.of_hasPullback ψ η[B]
    rwa [toUnit_unique (pullback.snd ψ η[B]) (toUnit T)] at hp

  have : IsReduced T.left := by
    have hp : IsPullback i.left (toUnit T).left ψ.left (η[B]).left := hker.map (Over.forget S)
    have : Etale (toUnit T).left := MorphismProperty.of_isPullback hp het
    have : IsReduced (𝟙_ (Over S)).left := by dsimp; infer_instance
    exact GlobalTheory.isReduced_of_smooth_of_isReduced (toUnit T).left
  have := hsep

  have hf : i ≫ g = toUnit T ≫ η[B'] := by
    apply Over.OverMorphism.ext
    refine ext_of_geometricPoints B'.hom _ _ (by rw [Over.w, Over.w]) ?_
    intro k _ _ x
    let xo : Over.mk (x ≫ T.hom) ⟶ T := Over.homMk x
    have e1 : (xo ≫ i) ≫ ψ = 1 := by
      rw [Category.assoc, hker.w, ← Category.assoc, Hom.one_def, toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    have e3 : xo ≫ (i ≫ g) = xo ≫ (toUnit T ≫ η[B']) := by
      rw [← Category.assoc, H k (x ≫ T.hom) (xo ≫ i) e1, Hom.one_def, ← Category.assoc,
        toUnit_unique (xo ≫ toUnit T) (toUnit _)]
    simpa only [xo, Over.comp_left, Over.homMk_left] using congrArg CommaMorphism.left e3
  have := hψ; have := hg; have := hfin; have := het; have := hsurj
  obtain ⟨β, hβ, hψβ⟩ := FlatQuotient.exists_desc ψ i g hker hf
  have : Epi ψ := FlatQuotient.epi_of_flat_surjective ψ
  exact ⟨β, hβ, hψβ, fun g'' h'' => (cancel_epi ψ).1 (h''.trans hψβ.symm)⟩

end GlobalTheory.HkFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertFamily

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

private theorem valAt'_add' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f + f') = valAt' y W f + valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W W' : X.Opens} (hle : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : valAt' y W' (resG X hle f) = valAt' y W f := by
  have hW : ⊤ ≤ y ⁻¹ᵁ W := fun x hx => hle (h hx)
  unfold valAt' valAt
  rw [dif_pos h, dif_pos hW]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

private theorem valAt'_constFn_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : y ≫ p = 𝟙 _) (a : ℂ) :
    valAt' y ⊤ (constFn p ⊤ a) = a := by
  have hq : ∀ (q : Sp ℂ ⟶ Sp ℂ) (e : ⊤ ≤ q ⁻¹ᵁ ⊤), q = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((q.appLE ⊤ ⊤ e).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a := by
    rintro q e rfl
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (((Sp ℂ).presheaf.map (𝟙 (Opposite.op (⊤ : (Sp ℂ).Opens)))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a
    simp
  have e0 : ⊤ ≤ y ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold valAt' valAt constFn
  rw [dif_pos e0]
  refine Eq.trans ?_ (hq (y ≫ p) (fun _ _ => trivial) hp)
  congr 1
  rw [← CommRingCat.comp_apply]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE y p ⊤ ⊤ ⊤ _ e0)

theorem ex_over (z : Fin g → ℂ) : (u.ex z).left ≫ A.hom = 𝟙 _ := by
  exact (Over.w (u.ex z)).trans (by simp)

theorem differentiableAt_val (z : Fin g → ℂ) (O : A.left.Opens) (f : Γ(A.left, O)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O) :
    DifferentiableAt ℂ (fun z' => valAt' (u.ex z').left O f) z := by
  obtain ⟨hO, hD⟩ := u.hol O f
  exact hD.differentiableAt (hO.mem_nhds h)

theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer (u.ex z).left (fun O f => fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w) where
  add O h f f' := by
    have e : (fun z' => valAt' (u.ex z').left O (f + f')) =
        (fun z' => valAt' (u.ex z').left O f) + fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_add' _ _ _ _
    rw [e, fderiv_add (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    rfl
  mul O h f f' := by
    have e : (fun z' => valAt' (u.ex z').left O (f * f')) =
        (fun z' => valAt' (u.ex z').left O f) * fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_mul_of_top_le_preimage_open _ _ _ _
    rw [e, fderiv_mul (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  res O O' hle h f := by
    have hev : (fun z' => valAt' (u.ex z').left O' (resG A.left hle f)) =ᶠ[nhds z]
        fun z' => valAt' (u.ex z').left O f := by
      filter_upwards [(u.hol O' (resG A.left hle f)).1.mem_nhds h] with z' hz'
      exact valAt'_resG _ hle hz' f
    rw [hev.fderiv_eq]

theorem fderiv_constFn (z w : Fin g → ℂ) (a : ℂ) :
    fderiv ℂ (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) z w = 0 := by
  have e : (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) = fun _ => a := by
    funext z'
    exact valAt'_constFn_top _ _ (ex_over u z') a
  rw [e]
  simp

theorem fn_eq {X : Scheme.{0}} (m : A.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    fn u m W f = fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  funext z'
  unfold fn valAt' valAt
  by_cases h : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]
    congr 1
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]

theorem existsUnique_vector : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z δ, PtDer ((u.ex z).left ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃! w, ∀ W f, z ∈ dom u m W → δ W f = fderiv ℂ (fn u m W f) z w := by
  intro P₀ u Hm χ hG R _ x₀ X p m _ hpb z δ hδ hc
  obtain ⟨hex, huniq⟩ := GlobalTheory.T.germDerivation_of_fibre_of_kills_base P₀.A R x₀ X p m hpb (u.ex z).left (ex_over u z)
  obtain ⟨δ₀, hδ₀, hc₀, hδδ₀⟩ := hex δ hδ hc
  obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.germDerivation_uniformised_abelianVariety_unique_vector P₀ u Hm χ hG z δ₀ hδ₀ hc₀
  refine ⟨w, fun W f hz => ?_, fun w' hw' => hwu w' fun O f hO => ?_⟩
  · rw [hδδ₀ W f hz, hw (m ⁻¹ᵁ W) ((m.app W).hom f) hz, fn_eq]
  · have hD := ptDer_fderiv u z w'
    have hpt : PtDer (u.ex z).left
        (fun O f => δ₀ O f - fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w') := by
      refine ⟨fun V hV f f' => ?_, fun V hV f f' => ?_, fun V V' hle hV f => ?_⟩
      · have h1 := hδ₀.add V hV f f'
        have h2 := hD.add V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.mul V hV f f'
        have h2 := hD.mul V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.res V V' hle hV f
        have h2 := hD.res V V' hle hV f
        linear_combination h1 - h2
    have key := huniq _ hpt (fun a => by
        have h1 := hc₀ a
        have h2 := fderiv_constFn u z w' a
        linear_combination h1 - h2)
      (fun V f hV => by
        have h1 := hδδ₀ V f hV
        have h2 := hw' V f hV
        rw [fn_eq] at h2
        linear_combination h2 - h1) O f hO
    exact sub_eq_zero.mp key

end GlobalTheory.KS.VertFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSetOfHilbertFunctionsFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.finite_setOf_hilbertFunctions_fibres : ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → {φ : ℕ → ℕ | ∃ (K : Type) (_ : Field K) (x : R →+* K), φ = dimDeg (I.map (MvPolynomial.map x))}.Finite := by
  first | exact @GlobalTheory.finite_setOf_dimDeg_map | exact GlobalTheory.finite_setOf_dimDeg_map | (intros; apply GlobalTheory.finite_setOf_dimDeg_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSymmCommutantKroneckerLeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_symm_commutant_kronecker_le : ∀ (K : Type) [Field K] (h : ℕ) (Em Ei : Matrix (Fin 8) (Fin 8) ℤ) (V : Submodule K (Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)), Em.IsSymm → Ei * Em = 1 → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose) → Module.finrank K V ≤ h * (h + 1) / 2 := by
  first | exact @GlobalTheory.ZM.finrank_symm_commutant_le | exact GlobalTheory.ZM.finrank_symm_commutant_le | (intros; apply GlobalTheory.ZM.finrank_symm_commutant_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquaresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.galoisCover_descent_and_cartesian_squares : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  first | exact @GlobalTheory.ZM.galoisCover_descent | exact GlobalTheory.ZM.galoisCover_descent | (intros; apply GlobalTheory.ZM.galoisCover_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorIsoExtendFromOpenContainingChartsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_iso_extend_from_open_containing_charts : ∀ (X Y : Scheme.{0}) (c : Y ⟶ X) [IsOpenImmersion c], (∀ N : LB X, (∀ a, N.U a ≤ c.opensRange) → (∃ t : (N.pull c).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen) ∧ ∀ M M' : LB X, (∀ a b, M.U a ⊓ M'.U b ≤ c.opensRange) → LBIso (M.pull c) (M'.pull c) → LBIso M M' := by
  first | exact @GlobalTheory.GenPush.gen_iso_of_charts_le_range | exact GlobalTheory.GenPush.gen_iso_of_charts_le_range | (intros; apply GlobalTheory.GenPush.gen_iso_of_charts_le_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_schemes_over_opens_along_cocycle : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (G : ∀ i, Over (U i).toScheme) (B : ∀ i j, Over (U i ⊓ U j).toScheme) (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i j, IsPullback (a i j) (B i j).hom (G i).hom (S.homOfLE inf_le_left)) → (∀ i j, IsPullback (b i j) (B i j).hom (G j).hom (S.homOfLE inf_le_right)) → (∀ i j k (T : Scheme.{0}) (x : T ⟶ (B i j).left) (y : T ⟶ (B j k).left) (z : T ⟶ (B i k).left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) → ∃ (A : Over S) (ψ : ∀ i, (G i).left ⟶ A.left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  first | exact @GlobalTheory.CocycleGlue.glue_over_opens | exact GlobalTheory.CocycleGlue.glue_over_opens | (intros; apply GlobalTheory.CocycleGlue.glue_over_opens <;> assumption)
end

