import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CohomZeroEquivSections
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AssocSetApplyOfPointwise
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

structure RActPre (X : Scheme.{0}) (Γ : Type) [Group Γ] where

  P : (Over X)ᵒᵖ ⥤ Type

  act : Γ → (P ⟶ P)
  act_one : act 1 = 𝟙 P
  act_mul : ∀ g h, act (g * h) = act g ≫ act h

variable {X : Scheme.{0}} (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

def assocSet (Q : RActPre X Γ) (ξ : Γ →* GL ι E) (T : Over X) :
    Submodule E (∀ (T' : Over X) (_ : T' ⟶ T) (_ : Q.P.obj (op T')), C(T'.left, ι → E)) where
  carrier := {f | (∀ ⦃T'' T' : Over X⦄ (v : T'' ⟶ T') (u : T' ⟶ T) (η : Q.P.obj (op T')) (t : T''.left),
      f T'' (v ≫ u) (Q.P.map v.op η) t = f T' u η (v.left.base t)) ∧
    ∀ ⦃T' : Over X⦄ (u : T' ⟶ T) (η : Q.P.obj (op T')) (γ : Γ) (t : T'.left),
      f T' u ((Q.act γ).app (op T') η) t = ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ f T' u η t}
  add_mem' {f g} hf hg := ⟨fun T'' T' v u η t => by
      simp only [Pi.add_apply, ContinuousMap.add_apply, hf.1 v u η t, hg.1 v u η t],
    fun T' u η γ t => by
      simp only [Pi.add_apply, ContinuousMap.add_apply, hf.2 u η γ t, hg.2 u η γ t, Matrix.mulVec_add]⟩
  zero_mem' := ⟨fun _ _ _ _ _ _ => rfl, fun T' u η γ t => by simp⟩
  smul_mem' c {f} hf := ⟨fun T'' T' v u η t => by
      simp only [Pi.smul_apply, ContinuousMap.smul_apply, hf.1 v u η t],
    fun T' u η γ t => by
      simp only [Pi.smul_apply, ContinuousMap.smul_apply, hf.2 u η γ t, Matrix.mulVec_smul]⟩

def assocRes (Q : RActPre X Γ) (ξ : Γ →* GL ι E) {T₁ T₂ : Over X} (w : T₁ ⟶ T₂) :
    assocSet E Q ξ T₂ →ₗ[E] assocSet E Q ξ T₁ where
  toFun f := ⟨fun T' u η => f.1 T' (u ≫ w) η,
    ⟨fun T'' T' v u η t => by simpa only [Category.assoc] using f.2.1 v (u ≫ w) η t,
      fun T' u η γ t => f.2.2 (u ≫ w) η γ t⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def assocPre (Q : RActPre X Γ) (ξ : Γ →* GL ι E) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} E) where
  obj T := ModuleCat.of (ULift.{1} E) (assocSet E Q ξ T.unop)
  map w := ModuleCat.ofHom
    { toFun := assocRes E Q ξ w.unop
      map_add' := (assocRes E Q ξ w.unop).map_add
      map_smul' := fun r f => (assocRes E Q ξ w.unop).map_smul r.down f }
  map_id T := ModuleCat.hom_ext (LinearMap.ext fun f => Subtype.ext (funext fun T' => funext fun u =>
    funext fun η => by
      change f.1 T' (u ≫ 𝟙 _) η = f.1 T' u η
      rw [Category.comp_id]))
  map_comp w₁ w₂ := ModuleCat.hom_ext (LinearMap.ext fun f => Subtype.ext (funext fun T' => funext fun u =>
    funext fun η => by
      change f.1 T' (u ≫ (w₂.unop ≫ w₁.unop)) η = f.1 T' ((u ≫ w₂.unop) ≫ w₁.unop) η
      rw [Category.assoc]))

abbrev cPre (X : Scheme.{0}) (ι : Type) : (Over X)ᵒᵖ ⥤ Type :=
  (Over.forget X).op ⋙ continuousMapPresheaf.{0} (ι → E)

theorem cPre_isSheaf (X : Scheme.{0}) (ι : Type) :
    Presieve.IsSheaf (Scheme.proetaleTopology.{0}.over X) (cPre E X ι) := by
  have h0 : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} (ι → E)) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf _)
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (CategoryTheory.Sheaf.over (⟨_, h0⟩ : Sheaf Scheme.proetaleTopology.{0} Type) X).cond

section
variable {E} (Q : RActPre X Γ) (ξ : Γ →* GL ι E)

theorem assocSet_nat {T : Over X} (f : assocSet E Q ξ T) {T'' T' : Over X} (v : T'' ⟶ T') (u : T' ⟶ T)
    (η : Q.P.obj (op T')) :
    f.1 T'' (v ≫ u) (Q.P.map v.op η) = (cPre E X ι).map v.op (f.1 T' u η) :=
  ContinuousMap.ext fun t => f.2.1 v u η t

end

theorem assocPre_isSheaf (Q : RActPre X Γ) (ξ : Γ →* GL ι E) :
    Presheaf.IsSheaf (Scheme.proetaleTopology.{0}.over X) (assocPre E Q ξ) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _), isSheaf_iff_isSheaf_of_type]
  intro T S hS x hx
  have hC := cPre_isSheaf E X ι
  let xv : ∀ ⦃Y : Over X⦄ (f : Y ⟶ T), S f → assocSet E Q ξ Y := fun Y f h => x f h

  have K : ∀ ⦃Y₁ Y₂ Z : Over X⦄ (f₁ : Y₁ ⟶ T) (f₂ : Y₂ ⟶ T) (h₁ : S f₁) (h₂ : S f₂) (a₁ : Z ⟶ Y₁) (a₂ : Z ⟶ Y₂),
      a₁ ≫ f₁ = a₂ ≫ f₂ → ∀ η, (xv f₁ h₁).1 Z a₁ η = (xv f₂ h₂).1 Z a₂ η := by
    intro Y₁ Y₂ Z f₁ f₂ h₁ h₂ a₁ a₂ e η
    have := hx a₁ a₂ h₁ h₂ e
    have h := congrArg (fun z => (show assocSet E Q ξ Z from z).1 Z (𝟙 Z) η) this
    change (xv f₁ h₁).1 Z (𝟙 Z ≫ a₁) η = (xv f₂ h₂).1 Z (𝟙 Z ≫ a₂) η at h
    simpa only [Category.id_comp] using h
  let fam : ∀ (T' : Over X) (_ : T' ⟶ T) (_ : Q.P.obj (op T')),
      Presieve.FamilyOfElements (cPre E X ι) (S.pullback ‹T' ⟶ T›).arrows := fun T' u η Y w hw =>
    (xv (w ≫ u) hw).1 Y (𝟙 Y) (Q.P.map w.op η)
  have famC : ∀ T' u η, (fam T' u η).Compatible := by
    intro T' u η Y₁ Y₂ Z g₁ g₂ w₁ w₂ hw₁ hw₂ e
    change (cPre E X ι).map g₁.op ((xv (w₁ ≫ u) hw₁).1 Y₁ (𝟙 Y₁) (Q.P.map w₁.op η)) =
      (cPre E X ι).map g₂.op ((xv (w₂ ≫ u) hw₂).1 Y₂ (𝟙 Y₂) (Q.P.map w₂.op η))
    rw [← assocSet_nat, ← assocSet_nat, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, e]
    exact K _ _ _ _ _ _ (by simp only [Category.comp_id, ← Category.assoc, e]) _
  let gl : ∀ (T' : Over X) (u : T' ⟶ T) (η : Q.P.obj (op T')), C(T'.left, ι → E) := fun T' u η =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).amalgamate (fam T' u η) (famC T' u η)
  have glv : ∀ T' (u : T' ⟶ T) η ⦃Y : Over X⦄ (w : Y ⟶ T') (hw : S (w ≫ u)),
      (cPre E X ι).map w.op (gl T' u η) = (xv (w ≫ u) hw).1 Y (𝟙 Y) (Q.P.map w.op η) := fun T' u η Y w hw =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).valid_glue (famC T' u η) w hw
  have sep : ∀ (T' : Over X) (u : T' ⟶ T) (c₁ c₂ : C(T'.left, ι → E)),
      (∀ ⦃Y : Over X⦄ (w : Y ⟶ T'), S (w ≫ u) → (cPre E X ι).map w.op c₁ = (cPre E X ι).map w.op c₂) →
        c₁ = c₂ := fun T' u c₁ c₂ h =>
    (hC _ (GrothendieckTopology.pullback_stable _ u hS)).isSeparatedFor.ext fun Y w hw => h w hw
  have mem : (fun T' u η => gl T' u η) ∈ assocSet E Q ξ T := by
    refine ⟨fun T'' T' v u η t => ?_, fun T' u η γ t => ?_⟩
    · have H : gl T'' (v ≫ u) (Q.P.map v.op η) = (cPre E X ι).map v.op (gl T' u η) := by
        refine sep T'' (v ≫ u) _ _ fun Y w hw => ?_
        rw [glv _ _ _ w hw, ← Functor.map_comp_apply (cPre E X ι), ← op_comp,
          glv T' u η (w ≫ v) (by simpa only [Category.assoc] using hw), op_comp, Functor.map_comp_apply]
        exact K _ _ _ _ _ _ (by simp only [Category.assoc]) _
      exact DFunLike.congr_fun H t
    · let M : ∀ Z : Over X, C(Z.left, ι → E) → C(Z.left, ι → E) := fun Z c =>
        ⟨fun t => ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ c t, continuous_const.matrix_mulVec c.continuous⟩
      have hM : ∀ c t, M T' c t = ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ c t := fun _ _ => rfl
      have hMn : ∀ ⦃Y⦄ (w : Y ⟶ T') c, (cPre E X ι).map w.op (M T' c) = M Y ((cPre E X ι).map w.op c) :=
        fun _ _ _ => rfl
      rw [← hM]
      have H : gl T' u ((Q.act γ).app (op T') η) = M T' (gl T' u η) := by
        refine sep T' u _ _ fun Y w hw => ?_
        rw [glv _ _ _ w hw, hMn, glv _ _ _ w hw]
        have hn : Q.P.map w.op ((Q.act γ).app (op T') η) = (Q.act γ).app (op Y) (Q.P.map w.op η) :=
          (NatTrans.naturality_apply (Q.act γ) w.op η).symm
        rw [hn]
        exact ContinuousMap.ext fun t => (xv (w ≫ u) hw).2.2 (𝟙 Y) _ γ t
      exact DFunLike.congr_fun H t
  refine ⟨⟨_, mem⟩, ?_, ?_⟩
  · intro Y f hf
    apply Subtype.ext
    funext Y' u η
    change gl Y' (u ≫ f) η = (xv f hf).1 Y' u η
    refine sep Y' (u ≫ f) _ _ fun Z w hw => ?_
    rw [glv _ _ _ w hw, ← assocSet_nat]
    exact K _ _ _ _ _ _ (by simp only [Category.id_comp, Category.assoc]) _
  · intro t' ht'
    apply Subtype.ext
    funext T' u η
    have ht : ∀ ⦃Y : Over X⦄ (f : Y ⟶ T) (hf : S f) η', (show assocSet E Q ξ T from t').1 Y (𝟙 Y ≫ f) η' =
        (xv f hf).1 Y (𝟙 Y) η' := fun Y f hf η' =>
      congrArg (fun z => (show assocSet E Q ξ Y from z).1 Y (𝟙 Y) η') (ht' f hf)
    change (show assocSet E Q ξ T from t').1 T' u η = gl T' u η
    refine sep T' u _ _ fun Y w hw => ?_
    rw [glv _ _ _ w hw, ← assocSet_nat, ← ht _ hw, Category.id_comp]

def assoc (Q : RActPre X Γ) (ξ : Γ →* GL ι E) : Shv E X := ⟨assocPre E Q ξ, assocPre_isSheaf E Q ξ⟩

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

def secAssoc (Q : RActPre X Γ) (ξ : Γ →* GL ι E) (T : Over X) : Sec (assoc E Q ξ) T ≃ₗ[E] assocSet E Q ξ T where
  toFun f := f
  invFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

abbrev ptOver (T' : Over X) (t : T'.left) : Over X := Over.mk (T'.left.fromSpecResidueField t ≫ T'.hom)

def ptHom (T' : Over X) (t : T'.left) : ptOver T' t ⟶ T' := Over.homMk (T'.left.fromSpecResidueField t) rfl

theorem ptHom_apply (T' : Over X) (t : T'.left) (y : (ptOver T' t).left) : (ptHom T' t).left.base y = t :=
  Scheme.fromSpecResidueField_apply t y

theorem assocSet_apply_of_pointwise (Q : RActPre X Γ) (ξ : Γ →* GL ι E) {T : Over X} (f : assocSet E Q ξ T)
    {T' : Over X} (u : T' ⟶ T) (η η' : Q.P.obj (op T')) (g : T'.left → Γ)
    (h : ∀ t, Q.P.map (ptHom T' t).op η' = (Q.act (g t)).app _ (Q.P.map (ptHom T' t).op η)) (t : T'.left) :
    f.1 T' u η' t = ((ξ (g t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ f.1 T' u η t := by
  let y : (ptOver T' t).left := IsLocalRing.closedPoint _
  have e1 := f.2.1 (ptHom T' t) u η' y
  have e2 := f.2.1 (ptHom T' t) u η y
  rw [ptHom_apply] at e1 e2
  rw [← e1, ← e2, h t]
  exact f.2.2 _ _ _ _

def trivTorsor (X : Scheme.{0}) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] : RActPre X Γ where
  P := (Over.forget X).op ⋙ continuousMapPresheaf.{0} Γ
  act γ :=
    { app := fun T => ↾fun (c : C(T.unop.left, Γ)) => c * ContinuousMap.const _ γ
      naturality := fun _ _ _ => rfl }
  act_one := by
    apply NatTrans.ext
    funext T
    ext (c : C(T.unop.left, Γ))
    exact ContinuousMap.ext fun t => mul_one (c t)
  act_mul g h := by
    apply NatTrans.ext
    funext T
    ext (c : C(T.unop.left, Γ))
    exact ContinuousMap.ext fun t => (mul_assoc (c t) g h).symm

def trivTorsor.ofC [TopologicalSpace Γ] [IsTopologicalGroup Γ] {T : Over X} (c : C(T.left, Γ)) :
    (trivTorsor X Γ).P.obj (op T) := c

def trivTorsor.toC [TopologicalSpace Γ] [IsTopologicalGroup Γ] {T : Over X} (g : (trivTorsor X Γ).P.obj (op T)) :
    C(T.left, Γ) := g

def assocTrivEquiv [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ξ : Γ →* GL ι E) (hξ : Continuous ξ) (T : Over X) :
    assocSet E (trivTorsor X Γ) ξ T ≃ₗ[E] C(T.left, ι → E) where
  toFun f := f.1 T (𝟙 T) (trivTorsor.ofC 1)
  invFun v := ⟨fun T' u g => ⟨fun t => ((ξ (trivTorsor.toC g t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ v (u.left.base t),
      (Units.continuous_val.comp (hξ.comp (continuous_inv.comp (trivTorsor.toC g).continuous))).matrix_mulVec
        (v.continuous.comp u.left.base.hom.continuous)⟩,
    ⟨fun T'' T' w u g t => rfl, fun T' u g γ t => by
      change ((ξ (trivTorsor.toC g t * γ)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ v (u.left.base t) =
        ((ξ γ⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ (((ξ (trivTorsor.toC g t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ v (u.left.base t))
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, _root_.mul_inv_rev]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    apply Subtype.ext
    funext T' u g
    ext t : 1
    have h1 := assocSet_apply_of_pointwise (trivTorsor X Γ) ξ f u (trivTorsor.ofC 1) g (trivTorsor.toC g)
      (fun t => ContinuousMap.ext fun y => by
        change trivTorsor.toC g ((ptHom T' t).left.base y) = 1 * trivTorsor.toC g t
        exact (congrArg (trivTorsor.toC g) (ptHom_apply T' t y)).trans (one_mul _).symm) t
    have h2 := f.2.1 u (𝟙 T) (trivTorsor.ofC 1) t
    rw [Category.comp_id] at h2
    change ((ξ (trivTorsor.toC g t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ f.1 T (𝟙 T) (trivTorsor.ofC 1) (u.left.base t) =
      f.1 T' u g t
    rw [h1, ← h2]
    rfl
  right_inv v := by
    ext t : 1
    change ((ξ ((1 : C(T.left, Γ)) t)⁻¹ : GL ι E) : Matrix ι ι E) *ᵥ v ((𝟙 T : T ⟶ T).left.base t) = v t
    simp

end GlobalTheory.Et.Rel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FirstChernClassMemHodgeFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.LogCris.CupModel

theorem isDPLog_unique {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {v a a' : B}
    (h : IsDPLog δ v a) (h' : IsDPLog δ v a') : a = a' := by
  obtain ⟨-, N, hN, rfl⟩ := h
  obtain ⟨-, N', hN', rfl⟩ := h'
  have key : ∀ (N M : ℕ), N ≤ M → (∀ n, N ≤ n → ((n - 1).factorial : B) * δ.dpow n (v - 1) = 0) →
      ∑ n ∈ Finset.Ico 1 N, (-1) ^ (n + 1) * ((n - 1).factorial : B) * δ.dpow n (v - 1) =
      ∑ n ∈ Finset.Ico 1 M, (-1) ^ (n + 1) * ((n - 1).factorial : B) * δ.dpow n (v - 1) := by
    intro N M hM h
    refine Finset.sum_subset (Finset.Ico_subset_Ico_right hM) fun n hn hn' => ?_
    rw [Finset.mem_Ico] at hn hn'
    rw [mul_assoc, h n (by omega), mul_zero]
  rw [key N (max N N') (le_max_left _ _) hN, key N' (max N N') (le_max_right _ _) hN']

theorem isDPLog_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {v a : B}
    (h : IsDPLog δ v a) : a ∈ J := by
  obtain ⟨hv, N, -, rfl⟩ := h
  refine J.sum_mem fun n hn => J.mul_mem_left _ (δ.dpow_mem ?_ hv)
  rw [Finset.mem_Ico] at hn
  omega

theorem isDPLog_eps : IsDPLog Ex.δJ (1 + DualNumber.eps) DualNumber.eps := by
  have hm : (DualNumber.eps : Ex.D) ∈ Ex.J := Ideal.subset_span rfl
  rw [IsDPLog, add_sub_cancel_left]
  refine ⟨hm, 2, fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have h1 := Ex.δJ.factorial_mul_dpow_eq_pow (n := m + 2) hm
    have h2 : (DualNumber.eps : Ex.D) ^ (m + 2) = 0 := by
      rw [pow_add, pow_two, DualNumber.eps_mul_eps, mul_zero]
    have h3 : IsUnit (((m + 2).factorial : ℕ) : Ex.D) := by
      have := (IsUnit.mk0 (((m + 2).factorial : ℕ) : ℚ) (by exact_mod_cast Nat.factorial_ne_zero _)).map
        (algebraMap ℚ Ex.D)
      simpa using this
    rw [h2] at h1
    rw [(h3.mul_right_eq_zero).1 h1, mul_zero]
  · simp [Ex.δJ.dpow_one hm]

variable {b : Base} {L : b.Fun}

theorem firstChernClass_mem_hodgeFiltration {E : LB L} {z : H L 2} (h : IsFirstChernClassOfLineBundle E z) : z ∈ Fil L 2 1 := by
  obtain ⟨u, ℓ, -, hℓ, rfl⟩ := h
  exact ⟨ℓ, rfl, fun s => Thick.J_le_pdPow_one _ (isDPLog_mem _ (hℓ s))⟩

theorem isNilpotent_of_mem (T : Thick L) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    simpa using this
  · obtain ⟨n, hn⟩ := T.adm.1 hp
    refine ⟨b.p ^ n, ?_⟩
    rw [← T.δ.factorial_mul_dpow_eq_pow hx]
    obtain ⟨c, hc⟩ : b.p ^ n ∣ (b.p ^ n).factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero (pow_ne_zero _ hp)) le_rfl
    rw [hc, Nat.cast_mul, Nat.cast_pow, hn, zero_mul, zero_mul]

theorem exists_unit_lift (T : Thick L) (v : (T.B ⧸ T.J)ˣ) :
    ∃ w : T.Bˣ, Units.map (Ideal.Quotient.mk T.J).toMonoidHom w = v := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v : T.B ⧸ T.J)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (v⁻¹ : (T.B ⧸ T.J)ˣ).val
  have h1 : a * c - 1 ∈ T.J := by
    rw [← Ideal.Quotient.eq, map_mul, ha, hc, map_one, Units.mul_inv]
  have h2 : IsUnit (a * c) := by
    have := (isNilpotent_of_mem T h1).isUnit_add_one
    rwa [sub_add_cancel] at this
  exact ⟨(isUnit_of_mul_isUnit_left h2).unit, Units.ext ha⟩

theorem firstChernClass_logComponent (i : L.ι) : IsFirstChernClassOfLineBundle (LB.ofComp i : LB L) 0 := by
  choose w hw using fun T : Thick L => exists_unit_lift T (T.v i)
  refine ⟨fun {T T'} φ => φ.u i * Units.map φ.φ.toMonoidHom (w T) * (w T')⁻¹, 0, fun {T T'} φ => ?_,
    fun s => ?_, Submodule.Quotient.mk_zero _⟩
  · have h := φ.hv i
    have e : Units.map (Ideal.Quotient.mk T'.J).toMonoidHom (Units.map φ.φ.toMonoidHom (w T)) =
        Units.map (Ideal.quotientMap T'.J φ.φ φ.hle).toMonoidHom (T.v i) := by
      rw [← hw T]; exact Units.ext rfl
    change _ = L.g T'.α T.α i T'.y
    rw [map_mul, map_mul, map_inv, hw T', e, ← h, mul_inv_cancel_comm]
  · have e : chainUnit (fun {T T'} φ => φ.u i * Units.map φ.φ.toMonoidHom (w T) * (w T')⁻¹) s = 1 := by
      have c : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map'_comp 0 1 2
      have key : ∀ {T T' T'' : Thick L} (f : T ⟶ T') (g : T' ⟶ T''),
          Units.map g.φ.toMonoidHom (f.u i * Units.map f.φ.toMonoidHom (w T) * (w T')⁻¹) *
            (g.u i * Units.map g.φ.toMonoidHom (w T') * (w T'')⁻¹) *
            ((f ≫ g).u i * Units.map (f ≫ g).φ.toMonoidHom (w T) * (w T'')⁻¹)⁻¹ = 1 := by
        intro T T' T'' f g
        have e1 : (f ≫ g).u i = g.u i * Units.map g.φ.toMonoidHom (f.u i) := rfl
        have e2 : Units.map (f ≫ g).φ.toMonoidHom (w T) =
          Units.map g.φ.toMonoidHom (Units.map f.φ.toMonoidHom (w T)) := Units.ext rfl
        rw [e1, e2, map_mul, map_mul, map_inv, mul_inv_eq_one]
        generalize Units.map g.φ.toMonoidHom (w T') = A
        generalize Units.map g.φ.toMonoidHom (f.u i) = B
        generalize Units.map g.φ.toMonoidHom (Units.map f.φ.toMonoidHom (w T)) = C
        calc B * C * A⁻¹ * (g.u i * A * (w T'')⁻¹) = (A⁻¹ * A) * (g.u i * B * C * (w T'')⁻¹) := by ac_rfl
          _ = _ := by rw [inv_mul_cancel, one_mul]
      have := congrArg Units.val (key (s.map' 0 1) (s.map' 1 2))
      rw [← c] at this
      exact this
    rw [e]
    exact isDPLog_one (s.obj (Fin.last 2)).δ

def rel (B : Type) [CommRing B] (q q' : Fin 2 → B) : Prop := ∃ u : Bˣ, ∀ i, q' i = u * q i

open Classical in

def ratio {B : Type} [CommRing B] (i j : Fin 2) (q : Fin 2 → B) : Bˣ :=
  if h : IsUnit (q i) ∧ IsUnit (q j) then h.1.unit * h.2.unit⁻¹ else 1

theorem ratio_eq {B : Type} [CommRing B] {i j : Fin 2} {q : Fin 2 → B} (a c : Bˣ) (ha : q i = a) (hc : q j = c) :
    ratio i j q = a * c⁻¹ := by
  have h : IsUnit (q i) ∧ IsUnit (q j) := ⟨ha ▸ a.isUnit, hc ▸ c.isUnit⟩
  rw [ratio, dif_pos h]
  congr 2 <;> ext <;> simp [ha, hc]

theorem ratio_rel {B : Type} [CommRing B] (i j : Fin 2) (q q' : Fin 2 → B) (h : rel B q q') :
    ratio i j q = ratio i j q' := by
  obtain ⟨u, hu⟩ := h
  by_cases h : IsUnit (q i) ∧ IsUnit (q j)
  · obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := h
    rw [ratio_eq a c ha.symm hc.symm, ratio_eq (u * a) (u * c) (by rw [hu, ← ha]; simp) (by rw [hu, ← hc]; simp),
      mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  · have h' : ¬ (IsUnit (q' i) ∧ IsUnit (q' j)) := by simpa [hu] using h
    rw [ratio, ratio, dif_neg h, dif_neg h']

abbrev linePt (k : Type) [CommRing k] : CommRingCat.{0} ⥤ Type where
  obj B := (k →+* B) × Quot (rel B)
  map φ := TypeCat.ofHom fun y => (φ.hom.comp y.1, Quot.map (fun q i => φ.hom (q i))
    (fun _ _ ⟨u, hu⟩ => ⟨Units.map φ.hom.toMonoidHom u, fun i => by simp [hu]⟩) y.2)
  map_id _ := by ext ⟨s, ⟨q⟩⟩ <;> rfl
  map_comp _ _ := by ext ⟨s, ⟨q⟩⟩ <;> rfl

abbrev line (k : Type) [CommRing k] (τ : k) (hτ : τ = 1) : LogFun k τ where
  ι := Fin 0
  A := Fin 2
  Pt := linePt k
  str y := y.1
  str_map _ _ := rfl
  In i _ y := Quot.lift (fun q => IsUnit (q i)) (fun _ _ ⟨u, hu⟩ => by simp [hu]) y.2
  in_map := fun {_ _ _} φ {y} h => by
    obtain ⟨s, ⟨q⟩⟩ := y
    exact IsUnit.map φ.hom h
  f _ i := i.elim0
  f_map i := i.elim0
  g _ _ i := i.elim0
  g_map i := i.elim0
  f_eq i := i.elim0
  g_self i := i.elim0
  g_comp i := i.elim0
  prod_f _ := by simp [hτ]
  prod_g _ _ := by simp

abbrev base1 : Base where
  R := ℚ
  I := ⊥
  γ := dividedPowersBot ℚ
  t := 1
  p := 0

abbrev lineL : base1.Fun := line _ _ (map_one _)

def degOne : LB lineL where
  g α β _ y := Quot.lift (ratio β α) (ratio_rel β α) y.2
  g_map := fun {α β B B'} φ {y} h1 h2 => by
    obtain ⟨s, ⟨q⟩⟩ := y
    obtain ⟨a, ha⟩ : IsUnit (q α) := h1
    obtain ⟨c, hc⟩ : IsUnit (q β) := h2
    change ratio β α (fun i => φ.hom (q i)) = Units.map _ (ratio β α q)
    rw [ratio_eq c a hc.symm ha.symm, ratio_eq (Units.map φ.hom.toMonoidHom c) (Units.map φ.hom.toMonoidHom a)
      (by rw [← hc]; rfl) (by rw [← ha]; rfl), map_mul, map_inv]
  g_self := fun {α B y} h => by
    obtain ⟨s, ⟨q⟩⟩ := y
    obtain ⟨a, ha⟩ : IsUnit (q α) := h
    change ratio α α q = 1
    rw [ratio_eq a a ha.symm ha.symm, mul_inv_cancel]
  g_comp := fun {α β γ B y} h1 h2 h3 => by
    obtain ⟨s, ⟨q⟩⟩ := y
    obtain ⟨a, ha⟩ : IsUnit (q α) := h1
    obtain ⟨c, hc⟩ : IsUnit (q β) := h2
    obtain ⟨e, he⟩ : IsUnit (q γ) := h3
    change ratio β α q * ratio γ β q = ratio γ α q
    rw [ratio_eq c a hc.symm ha.symm, ratio_eq e c he.symm hc.symm, ratio_eq e a he.symm ha.symm]
    calc c * a⁻¹ * (e * c⁻¹) = (c * c⁻¹) * (e * a⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel, one_mul]

open Polynomial in

theorem degOne_not_trivial : ¬ ∃ s : Fin 2 → ∀ {B : CommRingCat.{0}}, lineL.Pt.obj B → Bˣ,
    (∀ α {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : lineL.Pt.obj B), lineL.In α y →
      s α (lineL.Pt.map φ y) = Units.map φ.hom.toMonoidHom (s α y)) ∧
    ∀ α β {B : CommRingCat.{0}} (y : lineL.Pt.obj B), lineL.In α y → lineL.In β y →
      s α y = degOne.g α β y * s β y := by
  rintro ⟨s, hs, hg⟩
  let κ : (ℚ ⧸ (⊥ : Ideal ℚ)) →+* ℚ := Ideal.Quotient.lift _ (RingHom.id ℚ) fun a ha => ha
  let y0 : lineL.Pt.obj (CommRingCat.of ℚ[X]) := (C.comp κ, Quot.mk _ ![1, X])
  let y1 : lineL.Pt.obj (CommRingCat.of ℚ[X]) := (C.comp κ, Quot.mk _ ![X, 1])
  obtain ⟨c0, -, h0⟩ := Polynomial.isUnit_iff.1 (s 0 y0).isUnit
  obtain ⟨c1, hc1, h1⟩ := Polynomial.isUnit_iff.1 (s 1 y1).isUnit
  have key : ∀ t : ℚˣ, c0 = t * c1 := by
    intro t
    let z : lineL.Pt.obj (CommRingCat.of ℚ) := (κ, Quot.mk _ ![1, (t : ℚ)])
    have e0 : lineL.Pt.map (CommRingCat.ofHom (evalRingHom (t : ℚ))) y0 = z := by
      refine Prod.ext (RingHom.ext fun x => eval_C) (congrArg (Quot.mk _) (funext fun i => ?_))
      fin_cases i <;> simp
    have e1 : lineL.Pt.map (CommRingCat.ofHom (evalRingHom (t⁻¹ : ℚˣ).val)) y1 = z := by
      refine Prod.ext (RingHom.ext fun x => eval_C) (Quot.sound ⟨t, fun i => ?_⟩)
      fin_cases i <;> simp
    have f0 := hs 0 (CommRingCat.ofHom (evalRingHom (t : ℚ))) y0 isUnit_one
    have f1 := hs 1 (CommRingCat.ofHom (evalRingHom (t⁻¹ : ℚˣ).val)) y1 isUnit_one
    rw [e0] at f0
    rw [e1] at f1
    have g := hg 0 1 z isUnit_one t.isUnit
    have r : degOne.g 0 1 z = t * 1⁻¹ := ratio_eq (q := ![1, (t : ℚ)]) t 1 rfl rfl
    have v0 : ((s 0 z : ℚˣ) : ℚ) = c0 := by
      rw [f0]; change eval (t : ℚ) (s 0 y0).val = c0; rw [← h0, eval_C]
    have v1 : ((s 1 z : ℚˣ) : ℚ) = c1 := by
      rw [f1]; change eval (t⁻¹ : ℚˣ).val (s 1 y1).val = c1; rw [← h1, eval_C]
    rw [← v0, ← v1, g, r]; simp
  have a := key 1
  have c := key (-1)
  simp only [Units.val_one, Units.val_neg] at a c
  exact hc1.ne_zero (by linarith)

end GlobalTheory.LogCris.CupModel

namespace GlobalTheory.CatH

theorem cupC_one_one_model {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ ModuleCat.{0} R} (μ : Mult F)
    (f g : Cn F 1) (s : ComposableArrows C 2) :
    cupC μ (show 1 + 1 = 2 from rfl) f g s =
      μ.mul _ ((F.map (s.map' 1 2)).hom (f ((fr_mono 1 2 (by omega)).functor ⋙ s)))
        ((F.map (s.map' 2 2)).hom (g ((bk_mono 1 1 2 (by omega)).functor ⋙ s))) := rfl

end GlobalTheory.CatH
end
end

