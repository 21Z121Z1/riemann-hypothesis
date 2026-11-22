import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0001
import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0367
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeAffineSectionsSubalgebraTensor
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma scal {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (h : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) =
      (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appLE ⊤ W le_top ≫ C.germToFunctionField W =
      CommRingCat.ofHom (algebraMap k C.functionField) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k C.functionField))
  rw [h, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop] at h1
  have hm : (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op = 𝟙 _ :=
    (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map_id _
  have h2 : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) trivial := by
    rw [← cancel_mono (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv]
    refine h1.trans ?_
    simp only [Category.assoc]
    erw [hm, Category.comp_id]
  rw [h2]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact C.presheaf.germ_res (homOfLE le_top) (genericPoint C) _

theorem UpperTheory.baseChange_affine_sections_subalgebra_tensor :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsAffineOpen (u ⁻¹ᵁ W) ∧ ∃ e : L ⊗[k] B ≃+* Γ(X, u ⁻¹ᵁ W), (∀ (a : Γ(C, W)) (b : B), (b : C.functionField) = C.germToFunctionField W a → e ((1 : L) ⊗ₜ[k] b) = u.app W a) ∧ ∀ l : L, e (l ⊗ₜ[k] (1 : B)) = x.appLE ⊤ (u ⁻¹ᵁ W) le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l) := by
  intro k L _ _ _ C X _ c u x H _ hK W _ hW B hB
  have hu : IsAffineHom u := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine ⟨hW.preimage u, ?_⟩
  let g0 : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hinj : Function.Injective g0 := C.germToFunctionField_injective W
  have hmem : ∀ a, g0 a ∈ B := fun a => by
    have : g0 a ∈ (B : Set C.functionField) := by rw [hB]; exact ⟨a, rfl⟩
    exact this
  let g1 : Γ(C, W) →+* B := g0.codRestrict B hmem
  have hbij : Function.Bijective g1 := by
    refine ⟨fun a a' h => hinj (congrArg Subtype.val h), fun b => ?_⟩
    have : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
    rw [hB] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.ext ha⟩
  let gB : Γ(C, W) ≃+* B := RingEquiv.ofBijective g1 hbij
  let iB : CommRingCat.of B ≅ Γ(C, W) := gB.symm.toCommRingCatIso
  have hP := (GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback H hW).flip
  have hT := CommRingCat.isPushout_tensorProduct k L B
  have hP' : IsPushout (CommRingCat.ofHom (algebraMap k L)) (CommRingCat.ofHom (algebraMap k B))
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appLE ⊤ (u ⁻¹ᵁ W) le_top)
      (iB.hom ≫ u.app W) := by
    refine hP.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) iB.symm (Iso.refl _)
      (Scheme.ΓSpecIso_naturality _) ?_ (by simp) (by simp)
    rw [← Iso.inv_comp_eq]
    ext r
    exact congr($(scal c hK W).hom r)
  let E := IsPushout.isoIsPushout _ _ hT hP'
  refine ⟨E.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · intro a b hab
    have h1 := congr($(IsPushout.inr_isoIsPushout_hom _ _ hT hP').hom b)
    have h2 : iB.hom b = a := by
      apply hinj
      have h3 := congrArg Subtype.val (gB.apply_symm_apply b)
      exact h3.trans hab
    rw [← h2]
    exact h1
  · intro l
    have h1 := congr($(IsPushout.inl_isoIsPushout_hom _ _ hT hP').hom l)
    exact h1
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeFunctionFieldHomGenericPointComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.baseChange_functionField_hom_genericPoint_comp :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u → ∃ f : L →+* X.functionField, (∀ r : k, f (algebraMap k L r) = φ (algebraMap k C.functionField r)) ∧ ∀ (V : X.Opens) [Nonempty V] (l : L), X.germToFunctionField V (x.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l)) = f l := by
  intro k L _ _ _ C X _ _ c u x hpb _ hc φ hφ
  let F : CommRingCat.of L ⟶ X.functionField :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial
  have hx : X.fromSpecStalk (genericPoint X) ≫ x = Spec.map F := by
    have h1 := Scheme.toSpecΓ_naturality x
    have h2 : x = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, ← h1, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [h2, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    simp only [F, Category.assoc]
  have key : ∀ (V : X.Opens) (hV : genericPoint X ∈ V),
      x.appLE ⊤ V le_top ≫ X.presheaf.germ V (genericPoint X) hV =
        x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    intro V hV
    rw [← x.appLE_map (V := ⊤) (V' := V) le_top (homOfLE le_top).op, Category.assoc,
      X.presheaf.germ_res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨F.hom, ?_, ?_⟩
  · intro r
    have hsq : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k L) ≫ F) := by
      rw [Spec.map_comp, Spec.map_comp, hc, ← Category.assoc, hφ, Category.assoc, hpb.w,
        ← Category.assoc, hx]
    have := congrArg (fun g => g.hom r) (Spec.map_injective hsq)
    simpa using this.symm
  · intro V _ l
    have hV : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom l)) (key V hV)
    simpa [F] using this
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSemiMapOfLocallySurjectiveOnCocycles
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory.ConeLoc

open CochainComplex.mappingCone

private theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (k : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W t => P' W (t ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => k V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg), ?_, ?_⟩
  · exact GrothendieckTopology.bind_covering _ hS (fun V g hg => hT V g hg)
  · rintro W t ⟨V, e, g, hg, he, rfl⟩
    exact hT' V g hg W e he

private theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (k : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => k V g (hP V g hg)⟩

section
variable {R : Type} [CommRing R]

private theorem sm_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

private theorem sm_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ + ψ) a = Sec.map φ a + Sec.map ψ a := rfl

private theorem sm_sub {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ - ψ) a = Sec.map φ a - Sec.map ψ a := rfl

private theorem sm_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (-φ) a = - Sec.map φ a := rfl

private theorem sm_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have hn := φ.hom.naturality g.op
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, hn]

private theorem ms_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

private theorem ms_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ a b

private theorem ms_sub {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b :=
  map_sub (φ.hom.app (op U)).hom a b

private theorem ms_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map φ (-a) = - Sec.map φ a :=
  map_neg (φ.hom.app (op U)).hom a

private theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ a b

private theorem res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero (F.obj.map g.op).hom

private theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (h ≫ g) a = Sec.res h (Sec.res g a) := by
  simp [Sec.res]

end

variable {K M : Cx ℤ} (φ : K ⟶ M)

private theorem fst_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    Sec.map ((fst φ).1.v j k hjk) (Sec.map ((mappingCone φ).d i j) s) =
      - Sec.map (K.d j k) (Sec.map ((fst φ).1.v i j hij) s) := by
  rw [← sm_comp, d_fst_v φ i j k hij hjk, sm_neg, sm_comp]

private theorem snd_d (i j : ℤ) (hij : i + 1 = j) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    Sec.map ((snd φ).v j j (add_zero _)) (Sec.map ((mappingCone φ).d i j) s) =
      Sec.map (φ.f j) (Sec.map ((fst φ).1.v i j hij) s) + Sec.map (M.d i j) (Sec.map ((snd φ).v i i (add_zero i)) s) := by
  rw [← sm_comp, d_snd_v φ i j hij, sm_add, sm_comp, sm_comp]

private theorem decomp (i j : ℤ) (hij : i + 1 = j) {T : Scheme.{0}} (s : Sec ((mappingCone φ).X i) T) :
    s = Sec.map ((inl φ).v j i (by omega)) (Sec.map ((fst φ).1.v i j hij) s) +
      Sec.map ((inr φ).f i) (Sec.map ((snd φ).v i i (add_zero i)) s) := by
  have hid := id_X φ i j hij
  calc s = Sec.map (𝟙 _) s := rfl
    _ = _ := by rw [← hid]; rfl

private theorem d_inl (n : ℤ) {T : Scheme.{0}} (a : Sec (K.X n) T) (ha : Sec.map (K.d n (n + 1)) a = 0) :
    Sec.map ((mappingCone φ).d (n - 1) n) (Sec.map ((inl φ).v n (n - 1) (by omega)) a) =
      Sec.map ((inr φ).f n) (Sec.map (φ.f n) a) := by
  rw [← sm_comp, inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega), sm_sub, sm_comp, sm_comp, ha, ms_zero, sub_zero]

private theorem d_inr (i j : ℤ) {T : Scheme.{0}} (c : Sec (M.X i) T) :
    Sec.map ((mappingCone φ).d i j) (Sec.map ((inr φ).f i) c) = Sec.map ((inr φ).f j) (Sec.map (M.d i j) c) := by
  rw [← sm_comp, inr_f_d, sm_comp]

private theorem core (Q : Scheme.{0} → Prop) (hQ : ∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V)
    (H1 : ∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (b : Sec (M.X n) T), Sec.map (M.d n (n + 1)) b = 0 →
      Loc T fun V g => ∃ (a : Sec (K.X n) V) (c : Sec (M.X (n - 1)) V), Sec.map (K.d n (n + 1)) a = 0 ∧
        Sec.map (φ.f n) a = Sec.res g b + Sec.map (M.d (n - 1) n) c)
    (H2 : ∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (a : Sec (K.X n) T), Sec.map (K.d n (n + 1)) a = 0 →
      (∃ c : Sec (M.X (n - 1)) T, Sec.map (φ.f n) a = Sec.map (M.d (n - 1) n) c) →
      Loc T fun V g => ∃ a' : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) a' = Sec.res g a)
    (U : Scheme.{0}) (hU : Q U) (n : ℤ) (b : Sec ((mappingCone φ).X n) U)
    (hb : Sec.map ((mappingCone φ).d n (n + 1)) b = 0) :
    Loc U fun V g => ∃ c : Sec ((mappingCone φ).X (n - 1)) V,
      Sec.map ((mappingCone φ).d (n - 1) n) c = Sec.res g b := by
  have hdec := decomp φ n (n + 1) rfl b
  have hfd := fst_d φ n (n + 1) (n + 1 + 1) rfl rfl b
  have hsd := snd_d φ n (n + 1) rfl b
  set x := Sec.map ((fst φ).1.v n (n + 1) rfl) b with hx
  set y := Sec.map ((snd φ).v n n (add_zero n)) b with hy
  have hxd : Sec.map (K.d (n + 1) (n + 1 + 1)) x = 0 := by
    rw [hb, ms_zero] at hfd
    exact neg_eq_zero.mp hfd.symm
  have hxy : Sec.map (φ.f (n + 1)) x + Sec.map (M.d n (n + 1)) y = 0 := by
    rw [hb, ms_zero] at hsd
    exact hsd.symm
  have hyx : Sec.map (M.d n (n + 1)) y + Sec.map (φ.f (n + 1)) x = 0 := (add_comm _ _).trans hxy
  have hcob : ∃ c : Sec (M.X (n + 1 - 1)) U,
      Sec.map (φ.f (n + 1)) x = Sec.map (M.d (n + 1 - 1) (n + 1)) c := by
    refine ⟨Sec.map (M.XIsoOfEq (show n = n + 1 - 1 by omega)).hom (-y), ?_⟩
    rw [← sm_comp (M.XIsoOfEq (show n = n + 1 - 1 by omega)).hom (M.d (n + 1 - 1) (n + 1)),
      HomologicalComplex.XIsoOfEq_hom_comp_d, ms_neg]
    exact eq_neg_of_add_eq_zero_left hxy
  apply loc_bind (H2 U hU (n + 1) x hxd hcob)
  rintro V g ⟨a', ha'⟩
  set a := Sec.map (K.XIsoOfEq (show n + 1 - 1 = n by omega)).hom a' with ha
  have had : Sec.map (K.d n (n + 1)) a = Sec.res g x := by
    rw [ha, ← sm_comp (K.XIsoOfEq (show n + 1 - 1 = n by omega)).hom (K.d n (n + 1)),
      HomologicalComplex.XIsoOfEq_hom_comp_d, ha']
  set y' := Sec.res g y + Sec.map (φ.f n) a with hy'
  have hy'd : Sec.map (M.d n (n + 1)) y' = 0 := by
    rw [hy', ms_add, ← sm_res, ← sm_comp (φ.f n) (M.d n (n + 1)), φ.comm n (n + 1), sm_comp, had,
      ← sm_res, ← res_add, hyx, res_zero]
  have hdc1 : Sec.map ((mappingCone φ).d (n - 1) n) (Sec.map ((inl φ).v n (n - 1) (by omega)) a) =
      Sec.map ((inr φ).f n) (Sec.map (φ.f n) a) - Sec.map ((inl φ).v (n + 1) n (by omega)) (Sec.res g x) := by
    rw [← sm_comp ((inl φ).v n (n - 1) (by omega)) ((mappingCone φ).d (n - 1) n),
      inl_v_d φ n (n - 1) (n + 1) (by omega) (by omega), sm_sub, sm_comp, sm_comp, had]
  apply loc_mono (H1 V (hQ g hU) n y' hy'd)
  rintro W t ⟨a₂, c₂, ha₂, hφ⟩
  refine ⟨Sec.map ((inl φ).v n (n - 1) (by omega)) a₂ - Sec.map ((inr φ).f (n - 1)) c₂ -
    Sec.res t (Sec.map ((inl φ).v n (n - 1) (by omega)) a), ?_⟩
  rw [res_comp, hdec, ms_sub, ms_sub, d_inl φ n a₂ ha₂, d_inr, ← sm_res, hdc1, hφ, hy']
  simp only [sm_res, res_add, map_sub, map_add]
  abel

end UpperTheory.ConeLoc

theorem UpperTheory.bijective_semiMap_of_locally_surjective_on_cocycles :
    ∀ (R : Type) [CommRing R] (L B : Cx R) (ρ : SemiMap L B) (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) →
        (∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (b : Sec (B.X n) T), Sec.map (B.d n (n + 1)) b = 0 →
          Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (B.X (n - 1)) V), Sec.map (L.d n (n + 1)) a = 0 ∧
            ρ.app V n a = Sec.res g b + Sec.map (B.d (n - 1) n) c) →
        (∀ (T : Scheme.{0}), Q T → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
          (∃ c : Sec (B.X (n - 1)) T, ρ.app T n a = Sec.map (B.d (n - 1) n) c) →
          Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) →
        ∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec ((mappingCone ρ.toZ).X n) U), Sec.map ((mappingCone ρ.toZ).d n (n + 1)) b = 0 →
          Loc U fun V g => ∃ c : Sec ((mappingCone ρ.toZ).X (n - 1)) V, Sec.map ((mappingCone ρ.toZ).d (n - 1) n) c = Sec.res g b := by
  intro R _ L B ρ Q hQ H1 H2 U hU n b hb
  exact UpperTheory.ConeLoc.core ρ.toZ Q hQ (fun T hT m c hc => H1 T hT m c hc)
    (fun T hT m a ha hc => H2 T hT m a ha hc) U hU n b hb
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectedOfUnimodularSub
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

private theorem exists_mem_basicOpen {T : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(T, ⊤))
    (h : Ideal.span (Set.range v) = ⊤) (x : T) : ∃ j, x ∈ T.basicOpen (v j) := by
  by_contra hc
  push_neg at hc
  let φ : Γ(T, ⊤) →+* T.presheaf.stalk x := (T.presheaf.germ ⊤ x trivial).hom
  have hle : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal (T.presheaf.stalk x)).comap φ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have h1 := hc j
    rw [Scheme.mem_basicOpen_top] at h1
    exact h1
  rw [h, top_le_iff] at hle
  have h1 : (1 : Γ(T, ⊤)) ∈ (IsLocalRing.maximalIdeal (T.presheaf.stalk x)).comap φ := by
    rw [hle]; trivial
  simp at h1

private theorem isUnit_ι {T : Scheme.{0}} (f : Γ(T, ⊤)) : IsUnit ((T.basicOpen f).ι.appTop.hom f) := by
  have h := T.toRingedSpace.isUnit_res_basicOpen f
  have key : ∀ (W : T.Opens) (_ : W = T.basicOpen f) (hle : W ≤ ⊤),
      IsUnit ((T.presheaf.map (homOfLE hle).op).hom f) := by
    intro W hW hle
    subst hW
    exact h
  rw [Scheme.Opens.ι_appTop]
  exact key _ (by simp) _

private def sieveOf {T : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(T, ⊤)) : Sieve T where
  arrows V k := ∃ j, IsUnit (k.appTop.hom (v j))
  downward_closed := by
    rintro Y Z f ⟨j, hj⟩ g
    refine ⟨j, ?_⟩
    have h := hj.map g.appTop.hom
    rw [Scheme.Hom.comp_appTop]
    exact h

private theorem sieveOf_mem {T : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(T, ⊤))
    (h : Ideal.span (Set.range v) = ⊤) : sieveOf v ∈ Scheme.etaleTopology.{0} T := by
  choose j hj using exists_mem_basicOpen v h
  let 𝒰 : Scheme.Cover (Scheme.precoverage @Etale) T :=
    Scheme.Cover.mkOfCovers (Fin N) (fun j => (T.basicOpen (v j)).toScheme)
      (fun j => (T.basicOpen (v j)).ι) (fun x => ⟨j x, ⟨x, hj x⟩, rfl⟩) (fun _ => inferInstance)
  refine Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, ?_⟩
  rintro _ _ ⟨i⟩
  exact ⟨i, isUnit_ι _⟩

variable (D : Type) [CommRing D] (d : ℕ)

private abbrev Sm (X : RF) (p : ℕ) (T : Scheme.{0}) : Type :=
  {x : Fin (p + 1) → X.obj Γ(T, ⊤) // ∀ i j, X.rel (x i) (x j)}

private theorem rel_unit {N : ℕ} {A : Type} [CommRing A] {x y : (Vec D N).obj A} (h : (Vec D N).rel x y)
    (j : Fin N) (hy : IsUnit (y.1.2 j)) : IsUnit (x.1.2 j) := by
  obtain ⟨_, u, h2⟩ := h
  rw [h2]
  exact u.isUnit.mul hy

private theorem unimodular_of_unit_coord {A : Type} [CommRing A] {x : (Vec D (d + 1)).obj A} (j : Fin d)
    (h : IsUnit (x.1.2 j.castSucc)) : P2 x :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) h

private theorem cond1 (p : ℕ) (T : Scheme.{0}) (y : Sx (CN (Vec D (d + 1))) p T) :
    EtLoc T fun V k =>
      (∃ u : Sx (CN (L2 D d)) p V,
        sxMap (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) u = sxRes k y) ∨
      ∃ a : Sx (CN (L1 D d)) p V,
        sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a = sxRes k y := by
  let y' : Sm (Vec D (d + 1)) p T := y
  refine ⟨sieveOf (y'.1 0).1.2, sieveOf_mem _ (y'.1 0).2, ?_⟩
  rintro V k ⟨j, hj⟩
  have hrel : ∀ i, (Vec D (d + 1)).rel ((Vec D (d + 1)).map k.appTop.hom (y'.1 i))
      ((Vec D (d + 1)).map k.appTop.hom (y'.1 0)) := fun i => (Vec D (d + 1)).map_rel _ (y'.2 i 0)
  induction j using Fin.lastCases with
  | last =>
    right
    refine ⟨(⟨fun i => ⟨(Vec D (d + 1)).map k.appTop.hom (y'.1 i), rel_unit D (hrel i) _ hj⟩,
      fun i j => (Vec D (d + 1)).map_rel _ (y'.2 i j)⟩ : Sm (L1 D d) p V), rfl⟩
  | cast j =>
    left
    refine ⟨(⟨fun i => ⟨(Vec D (d + 1)).map k.appTop.hom (y'.1 i),
      unimodular_of_unit_coord D d j (rel_unit D (hrel i) _ hj)⟩,
      fun i j => (Vec D (d + 1)).map_rel _ (y'.2 i j)⟩ : Sm (L2 D d) p V), rfl⟩

private theorem cond2 (p : ℕ) (T : Scheme.{0}) (a b : Sx (CN (L1 D d)) p T)
    (h : sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a =
      sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) b) :
    EtLoc T fun V k => sxRes k a = sxRes k b ∨ ∃ u : Sx (CN (L2 D d)) p V,
      sxMap (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) u =
        sxRes k (sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a) := by
  have hab : a = b := by
    let a' : Sm (L1 D d) p T := a
    let b' : Sm (L1 D d) p T := b
    have h' : ∀ i, (a'.1 i).1 = (b'.1 i).1 := fun i => congrFun (congrArg Subtype.val h) i
    exact Subtype.ext (funext fun i => Subtype.ext (h' i))
  exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V k _ => Or.inl (by rw [hab])⟩

private theorem mono2 : Mono (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) := by
  have h : ∀ n, Mono ((CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)).app n) := by
    intro n
    have h' : ∀ U, Mono (((CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)).app n).app U) := by
      intro U
      rw [mono_iff_injective]
      intro a b hab
      let a' : {x : Fin (n.unop.len + 1) → (L2 D d).obj Γ(U.unop, ⊤) // ∀ i j, (L2 D d).rel (x i) (x j)} := a
      let b' : {x : Fin (n.unop.len + 1) → (L2 D d).obj Γ(U.unop, ⊤) // ∀ i j, (L2 D d).rel (x i) (x j)} := b
      have h2 : ∀ i, (a'.1 i).1 = (b'.1 i).1 := fun i => congrFun (congrArg Subtype.val hab) i
      exact Subtype.ext (funext fun i => Subtype.ext (h2 i))
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

private theorem isPb : IsPullback (CN.map (bothToSecond D d) (both_to_second_relation D d)) (CN.map (bothToFirst D d) (both_to_first_relation D d))
    (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map))
    (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) := by
  refine IsPullback.of_forall_isPullback_app fun n => IsPullback.of_forall_isPullback_app fun U => ?_
  rw [Types.isPullback_iff]
  refine ⟨rfl, fun x y h => ?_, fun x₂ x₃ h => ?_⟩
  · let x' : {x : Fin (n.unop.len + 1) → (lift_levelP_alt₂ D d).obj Γ(U.unop, ⊤) // ∀ i j, (lift_levelP_alt₂ D d).rel (x i) (x j)} := x
    let y' : {x : Fin (n.unop.len + 1) → (lift_levelP_alt₂ D d).obj Γ(U.unop, ⊤) // ∀ i j, (lift_levelP_alt₂ D d).rel (x i) (x j)} := y
    have h1 : ∀ i, (x'.1 i).1 = (y'.1 i).1 := fun i =>
      congrArg (fun z : (L2 D d).obj Γ(U.unop, ⊤) => z.1) (congrFun (congrArg Subtype.val h.1) i)
    exact Subtype.ext (funext fun i => Subtype.ext (h1 i))
  · let a : {x : Fin (n.unop.len + 1) → (L2 D d).obj Γ(U.unop, ⊤) // ∀ i j, (L2 D d).rel (x i) (x j)} := x₂
    let b : {x : Fin (n.unop.len + 1) → (L1 D d).obj Γ(U.unop, ⊤) // ∀ i j, (L1 D d).rel (x i) (x j)} := x₃
    have h' : ∀ i, (a.1 i).1 = (b.1 i).1 := fun i => congrFun (congrArg Subtype.val h) i
    let z : {x : Fin (n.unop.len + 1) → (lift_levelP_alt₂ D d).obj Γ(U.unop, ⊤) // ∀ i j, (lift_levelP_alt₂ D d).rel (x i) (x j)} :=
      ⟨fun i => ⟨(a.1 i).1, (a.1 i).2, by rw [h' i]; exact (b.1 i).2⟩, fun i j => a.2 i j⟩
    refine ⟨z, ?_, ?_⟩
    · exact Subtype.ext (funext fun i => Subtype.ext rfl)
    · exact Subtype.ext (funext fun i => Subtype.ext (h' i))

private theorem eqv_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine (Function.bijective_iff_has_inverse).2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

end UpperTheory

theorem UpperTheory.connected_of_unimodular_sub :
    LeafExc → A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) (d : ℕ) (D : Type) [CommRing D], Conn R F c (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) → Conn R F c (CN.map (bothToFirst D d) (both_to_first_relation D d)) := by
  intro hE hA R _ F c d D _ hC
  haveI := UpperTheory.mono2 D d
  have h := (hE hA R F c (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map))
    (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map))
    (UpperTheory.cond1 D d) (UpperTheory.cond2 D d)).1 hC
  have hp := UpperTheory.isPb D d
  refine (conn_sq F c (CN.map (bothToFirst D d) (both_to_first_relation D d)) _ hp.isoPullback.hom (𝟙 _) ?_
    (UpperTheory.eqv_iso F _) (UpperTheory.eqv_iso F (Iso.refl _))).2 h
  rw [Category.comp_id, IsPullback.isoPullback_hom_snd]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteNonemptyAffineCoverOfIntegral
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_finite_nonempty_affine_cover_of_integral :
    ∀ (C : Scheme.{0}) [CompactSpace C] [IsIntegral C], ∃ (n : ℕ) (U : Fin n → C.Opens), (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Nonempty (U i)) ∧ (0 < n) ∧ ∀ y : C, ∃ i, y ∈ U i := by
  intro C _ _
  have hex : ∀ y : C, ∃ W : C.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hWa hyW using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set C))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  obtain ⟨y0⟩ := (inferInstance : Nonempty C)
  have htne : t.Nonempty := by
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y0))
    exact ⟨i, hi⟩
  refine ⟨t.card, fun i => W (t.equivFin.symm i), fun i => hWa _,
    fun i => ⟨⟨_, hyW _⟩⟩, Finset.card_pos.2 htne, fun y => ?_⟩
  obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨i, hi⟩, ?_⟩
  simpa using hy
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFunctionFieldHomGermOfSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_functionField_hom_germ_of_surjective :
    ∀ {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (u : X ⟶ C), Surjective u → ∃ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u ∧ ∀ (W : C.Opens) [Nonempty W] [Nonempty (u ⁻¹ᵁ W)] (a : Γ(C, W)), φ (C.germToFunctionField W a) = X.germToFunctionField (u ⁻¹ᵁ W) (u.app W a) := by
  intro C X _ _ u hu
  have hgX : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hcl : closure ({u (genericPoint X)} : Set C) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    have h1 := image_closure_subset_closure_image (s := ({genericPoint X} : Set X)) u.continuous
    rw [Set.image_singleton, hgX, Set.image_univ,
      (Surjective.surj (f := u)).range_eq] at h1
    exact h1
  have hsp : u (genericPoint X) ⤳ genericPoint C := by
    rw [specializes_iff_mem_closure, hcl]
    trivial
  refine ⟨(C.presheaf.stalkSpecializes hsp ≫ u.stalkMap (genericPoint X)).hom, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro W _ _ a
    have hmem : u (genericPoint X) ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff (u ⁻¹ᵁ W).isOpen).mpr (by simpa using ‹Nonempty (u ⁻¹ᵁ W)›)
    change (u.stalkMap (genericPoint X)).hom ((C.presheaf.stalkSpecializes hsp).hom
      ((C.presheaf.germ W (genericPoint C) _).hom a)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply (hy := _) (h := hsp)]
    exact Scheme.Hom.germ_stalkMap_apply u W (genericPoint X) hmem a
end

