import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
section
noncomputable section

namespace GlobalTheory.AbLaw.Cube

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem corr_of_val_section {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {Y : Over S}
    (hY : Function.Surjective Y.hom.appTop.hom) (e : 𝟙_ (Over S) ⟶ Y) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y.left ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y.left ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good L y J → val u e.left y J = val u' e.left y J) : LB.Gen.Corr L φ ε φ' ε' u u' :=
  corr_of_val hL fun y J hJ => gen_unique' hL hF Y.hom e.left (Over.w e) hY hu hu' h _ _ y J hJ

theorem surj_tensor (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S}
    (hT : Function.Surjective T.hom.appTop.hom) : Function.Surjective (A ⊗ T).hom.appTop.hom := by
  rw [← Over.w (snd A T)]
  exact surj_comp (surj_snd hG hA T) hT

variable [IsCommMonObj A] {L : LB A.left}

omit [IsCommMonObj A] in
theorem prod_theta {U : Type} [CommGroup U] (h : ((G3 A).left ⟶ A.left) → U) :
    ∏ I : thK.{0}, h (thφ A (x3 A) I) ^ thε I =
      ∏ I : thK.{0}, h ((lift (x3 A 0) (lift (x3 A 1) (x3 A 2))).left ≫ thφ A (x3 A) I) ^ thε I := by
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by ext <;> simp [x3]
  rw [e]
  exact Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (Category.id_comp _).symm

omit [GrpObj A] [IsCommMonObj A] in
theorem oneGen_isGen {Y : Scheme.{0}} : (LB.oneGen L (Y := Y)).IsGen :=
  fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

def IsNormalised (t : LB.Gen (Theta A L)) : Prop :=
  ∀ (y : (𝟙_ (Over S)).left) J, Good L y J →
    val (L := L) (φ := thφ A (x3 A)) (ε := thε) t (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J = 1

theorem exists_normalised (hL : L.IsLB) (t : LB.Gen (Theta A L)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (Theta A L), t'.IsGen ∧ IsNormalised t' := by
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _
          (c := ∏ i, k (thφ A (x3 A) i) ^ thε i) rfl
          (DVR.prod_neg _ _ (prod_cub (1 : G3 A ⟶ A) 1 1 k))) ?_
      simp)
    (LB.mulGen L (thφ A (x3 A)) thε _ _ t (LB.invGen L _ _
      (LB.pullGen L (thφ A (x3 A)) thε t (lift (1 : G3 A ⟶ A) (lift 1 1)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨t', ht', fun y J hJ => ?_⟩
  refine (hv _ _ y J hJ).trans ((val_mul hJ _ _ _).trans ((congrArg _ (val_inv _ _)).trans
    (mul_inv_eq_one.2 (Eq.symm ((val_pull hJ _ _ _).trans ?_)))))
  rw [← Over.comp_left, comp_lift, comp_lift, MonObj.comp_one]
  rfl

theorem IsNormalised.pull {t : LB.Gen (Theta A L)} (ht : IsNormalised t) {T : Over S} (e : 𝟙_ (Over S) ⟶ T)
    {a b c : T ⟶ A} (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1) {y J} (hJ : Good L y J) :
    val (LB.pullGen L (thφ A (x3 A)) thε t (lift a (lift b c)).left) e.left y J = 1 := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift, ha, hb, hc]
  exact ht y J hJ

def cubicalOfNormalised (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (M : RigLB A) (t : LB.Gen (Theta A M.L))
    (ht : t.IsGen) (hn : IsNormalised t) : CubicalStr A M :=
  have s₁ := (hG _ _ hA).2
  have s₂ := surj_tensor hG hA s₁
  have s₃ := surj_tensor hG hA s₂
  have s₄ := surj_tensor hG hA s₃
  { t := t
    isGen := ht
    face := fun i => by
      have key : ∀ a b c : G2 A ⟶ A, lift 1 1 ≫ a = (1 : 𝟙_ (Over S) ⟶ A) → lift 1 1 ≫ b = (1 : 𝟙_ (Over S) ⟶ A) →
          lift 1 1 ≫ c = (1 : 𝟙_ (Over S) ⟶ A) → a = 1 ∨ b = 1 ∨ c = 1 →
          LB.Gen.Corr M.L _ _ (Y := (G2 A).left) _ _
            (LB.pullGen M.L (thφ A (x3 A)) thε t (lift a (lift b c)).left) (LB.oneGen M.L) := by
        intro a b c ha hb hc h
        refine corr_of_val_section M.isLB s₂ (lift 1 1) (fun V _ k => ?_) (DVR.pullGen_isGen _ _ _ _ ht _) oneGen_isGen
          (fun y J hJ => (hn.pull _ ha hb hc hJ).trans (val_one _).symm)
        refine (Fintype.prod_empty _).trans (Eq.trans ?_ (prod_cub a b c k).symm)
        apply Additive.ofMul.injective
        rcases h with rfl | rfl | rfl <;> simp only [_root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;> abel
      fin_cases i
      · exact key 1 (x2 A 0) (x2 A 1) (MonObj.comp_one _) (by simp [x2]) (by simp [x2]) (.inl rfl)
      · exact key (x2 A 0) 1 (x2 A 1) (by simp [x2]) (MonObj.comp_one _) (by simp [x2]) (.inr (.inl rfl))
      · exact key (x2 A 0) (x2 A 1) 1 (by simp [x2]) (by simp [x2]) (MonObj.comp_one _) (.inr (.inr rfl))
    cubeSymmetric_swap_first := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 1) (x3 A 0)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cubeSymmetric_swap_last := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 2) (x3 A 1), mul_right_comm (x3 A 0) (x3 A 2)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cocycle := by
      let e : 𝟙_ (Over S) ⟶ G4 A := lift 1 (lift 1 (lift 1 1))
      have e₀ : e ≫ x4 A 0 = 1 := by simp [e, x4]
      have e₁ : e ≫ x4 A 1 = 1 := by simp [e, x4]
      have e₂ : e ≫ x4 A 2 = 1 := by simp [e, x4]
      have e₃ : e ≫ x4 A 3 = 1 := by simp [e, x4]
      have f₀ : e ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
      have f₁ : e ≫ padd A (x4 A 1) (x4 A 2) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
      refine corr_of_val_section M.isLB s₄ e (fun V _ k => ?_)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (fun y J hJ => ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e f₀ e₂ e₃ hJ) (hn.pull e e₀ e₁ e₃ hJ))).trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e e₀ f₁ e₃ hJ) (hn.pull e e₁ e₂ e₃ hJ))).symm)
      refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0) (x4 A 1 * x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 1) (x4 A 2) (x4 A 3) k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0 * x4 A 1) (x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 0) (x4 A 1) (x4 A 3) k)).symm)
      apply Additive.ofMul.injective
      simp only [_root_.mul_assoc (x4 A 0), ofMul_mul, ofMul_inv]
      abel }

theorem cubical_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {M : RigLB A} (c c' : CubicalStr A M) :
    LB.Gen.Corr M.L _ _ _ _ c.t c'.t :=
  corr_of_val_section M.isLB (surj_tensor hG hA (surj_tensor hG hA (hG _ _ hA).2)) (lift 1 (lift 1 1))
    (φ := thφ A (x3 A)) (ε := thε) (φ' := thφ A (x3 A)) (ε' := thε) (fun _ _ _ => rfl) c.isGen c'.isGen
    fun _ _ hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm

theorem cube_of_gen : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB →
    ∃ t : LB.Gen (Theta P.A M), t.IsGen) → CubeSt := by
  intro hG hT S _ P M _
  have := P.isAb.comm
  obtain ⟨t, ht⟩ := hT S P M.L M.isLB
  obtain ⟨t', ht', hn⟩ := exists_normalised M.isLB t ht
  exact ⟨⟨cubicalOfNormalised hG P.isAb M t' ht' hn⟩, cubical_unique hG P.isAb⟩

end GlobalTheory.AbLaw.Cube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilMul

theorem exists_ratio {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := hp (res le (t.s PEmpty.elim)).val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans ((gs_unit r z ⊤ trivial _).symm.trans
    ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

def tv {T T' : Over S} (θ : ThetaGrp A L k T) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left)
    (J : (T'.left ⟶ A.left) → L.ι) : (T'.left.presheaf.stalk z)ˣ :=
  val (L := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (lift t a).left z J

theorem lift_translPt {T T' : Over S} (x : T ⟶ A) (t : T' ⟶ T) (a : T' ⟶ A) :
    lift t a ≫ translPt A x = (t ≫ x) * a := by
  rw [translPt, ← Category.assoc, comp_lift, lift_snd, lift_fst_assoc, Hom.mul_def]

theorem lift_translT {T T' : Over S} (x : T ⟶ A) (t : T' ⟶ T) (a : T' ⟶ A) :
    lift t a ≫ translT A x = lift t ((t ≫ x) * a) := by
  rw [translT, comp_lift, lift_fst, lift_translPt]

theorem prod_theta {T T' : Over S} (x : T ⟶ A) (t : T' ⟶ T) (a : T' ⟶ A) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t a).left ≫ ![(snd T A).left, (translPt A x).left] i) ^ (![k, -k] i) =
      h a.left ^ k * h ((t ≫ x) * a).left ^ (-k) := by
  rw [Fin.prod_univ_two]
  show h (lift t a ≫ snd T A).left ^ k * h (lift t a ≫ translPt A x).left ^ (-k) = _
  rw [lift_snd, lift_translPt]

theorem prod_theta_id {T : Over S} (x : T ⟶ A) {U : Type} [CommGroup U]
    (h : ((T ⊗ A).left ⟶ A.left) → U) :
    ∏ i : Fin 2, h (![(snd T A).left, (translPt A x).left] i) ^ (![k, -k] i) =
      h (snd T A).left ^ k * h ((fst T A ≫ x) * snd T A).left ^ (-k) := by
  rw [Fin.prod_univ_two]
  rfl

theorem val_pull_tv {T T₁ T' : Over S} (θ : ThetaGrp A L k T) (t : T₁ ⟶ T) (a : T₁ ⟶ A) (ρ : T' ⟶ T₁)
    {z : T'.left} {J} (hJ : Good L z J) :
    val (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (lift t a).left)
      ρ.left z J = tv θ (ρ ≫ t) (ρ ≫ a) z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift]; rfl

def CommV {T T₀ : Over S} (θx θy : ThetaGrp A L k T) (g : T ⟶ T₀) (c : Γ(T₀.left, ⊤)ˣ) : Prop :=
  ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left) (J), Good L z J →
    tv θx t a z J * tv θy t ((t ≫ θx.pt) * a) z J =
      tv θy t a z J * tv θx t ((t ≫ θy.pt) * a) z J * gm (t ≫ g).left z ⊤ c

theorem val_const {T T' : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) (t : T' ⟶ overRes V) (a : T' ⟶ A)
    (z : T'.left) (J) :
    val (constGen A L (unitRes V c)) (lift t a).left z J = gm (t ≫ overResι V).left z ⊤ c := by
  have hm : (lift t a).left z ∈ LB.wchart L (PEmpty.elim : PEmpty → ((overRes V ⊗ A).left ⟶ A.left)) PEmpty.elim :=
    Set.mem_iInter.2 fun k => k.elim
  rw [val_of _ _ z J PEmpty.elim (fun k => k.elim)]
  refine (gm_res _ z le_top hm _).trans ((gm_pull (lift t a).left (fst (overRes V) A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]
  exact gm_pull t.left V.ι z ⊤ trivial c

theorem commIs_iff (hL : L.IsLB) {T : Over S} (V : T.left.Opens) (θx θy : ThetaGrp A L k (overRes V))
    (c : Γ(T.left, ⊤)ˣ) : CommIsOf A L k θx θy (unitRes V c) ↔ CommV θx θy (overResι V) c := by
  have e : ∀ (θ θ' : ThetaGrp A L k (overRes V)) (T' : Over S) (t : T' ⟶ overRes V) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (lift t a).left z J =
        tv θ t a z J * tv θ' t ((t ≫ θ.pt) * a) z J := fun θ θ' T' t a z J hJ => by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
    rw [← Over.comp_left, lift_translT]; rfl
  constructor
  · intro h T' t a z J hJ
    exact (e θx θy _ t a z J hJ).symm.trans ((val_corr hJ h (lift t a).left).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (e θy θx _ t a z J hJ) (val_const V c t a z J))))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    have i : 𝟙 (overRes V ⊗ A).left = (lift (fst (overRes V) A) (snd (overRes V) A)).left := by
      rw [lift_fst_snd]; rfl
    rw [i]
    exact (e θx θy _ _ _ y J hJ).trans ((h _ _ _ y J hJ).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (e θy θx _ _ _ y J hJ) (val_const V c _ _ y J))).symm)

theorem exists_restrict (hL : L.IsLB) {T T₁ : Over S} (θ : ThetaGrp A L k T) (f : T₁ ⟶ T) :
    ∃ θ₁ : ThetaGrp A L k T₁, θ₁.pt = f ≫ θ.pt ∧ ∀ (T' : Over S) (t : T' ⟶ T₁) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → tv θ₁ t a z J = tv θ (t ≫ f) a z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T₁ A).left, (translPt A (f ≫ θ.pt)).left])
    (ε' := ![k, -k]) (fun U _ h => by
      refine (prod_theta θ.pt (fst T₁ A ≫ f) (snd T₁ A) h).trans ?_
      rw [prod_theta_id, Category.assoc])
    (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
      (lift (fst T₁ A ≫ f) (snd T₁ A)).left) (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  refine ⟨⟨f ≫ θ.pt, u, hu⟩, rfl, fun T' t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_pull_tv θ _ _ (lift t a) hJ).trans ?_)
  rw [lift_fst_assoc, lift_snd]

theorem exists_mul [IsCommMonObj A] (hL : L.IsLB) {T : Over S} (θ θ' : ThetaGrp A L k T) :
    ∃ θ₁ : ThetaGrp A L k T, θ₁.pt = θ.pt * θ'.pt ∧ ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ A) (z : T'.left) (J),
      Good L z J → tv θ₁ t a z J = tv θ t a z J * tv θ' t ((t ≫ θ.pt) * a) z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A (θ.pt * θ'.pt)).left])
    (ε' := ![k, -k]) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_theta_id θ.pt h)
        (prod_theta θ'.pt (fst T A) ((fst T A ≫ θ.pt) * snd T A) h))).trans ?_
      rw [prod_theta_id, MonObj.comp_mul, mul_comm (fst T A ≫ θ.pt) (fst T A ≫ θ'.pt),
        _root_.mul_assoc (fst T A ≫ θ'.pt)]
      simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ'.pt).left] ![k, -k] θ'.φ
      (lift (fst T A) ((fst T A ≫ θ.pt) * snd T A)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θ.isGen (DVR.pullGen_isGen _ _ _ _ θ'.isGen _))
  refine ⟨⟨θ.pt * θ'.pt, u, hu⟩, rfl, fun T' t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_pull_tv θ' _ _ (lift t a) hJ).trans ?_)))
  rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, lift_fst]

theorem ratio_const (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) {T' : Over S} (t : T' ⟶ T) (a b : T' ⟶ A) {z : T'.left} {J}
    (hJ : Good L z J) : tv θ t a z J * (tv θ' t a z J)⁻¹ = tv θ t b z J * (tv θ' t b z J)⁻¹ := by
  obtain ⟨x, φ, hφ⟩ := θ
  obtain ⟨x', φ', hφ'⟩ := θ'
  obtain rfl : x = x' := h
  obtain ⟨c, hc⟩ := exists_ratio hL (snd A T).left (surj_snd hG hA T)
    (DVR.pullGen_isGen _ _ _ _ hφ (lift (snd A T) (fst A T)).left)
    (DVR.pullGen_isGen _ _ _ _ hφ' (lift (snd A T) (fst A T)).left)
  have key : ∀ a : T' ⟶ A, (tv ⟨x, φ, hφ⟩ t a z J * (tv ⟨x, φ', hφ'⟩ t a z J)⁻¹).val = gs t.left z ⊤ c := fun a => by
    have e₁ := val_pull_tv ⟨x, φ, hφ⟩ (snd A T) (fst A T) (lift a t) hJ
    have e₂ := val_pull_tv ⟨x, φ', hφ'⟩ (snd A T) (fst A T) (lift a t) hJ
    rw [lift_fst, lift_snd] at e₁ e₂
    have := hc _ (lift a t).left z J hJ
    rw [← Over.comp_left, lift_snd] at this
    rw [← e₁, ← e₂]
    exact this
  exact Units.ext ((key a).trans (key b).symm)

theorem CommV.congr (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T T₀ : Over S}
    {θx θy θx' θy' : ThetaGrp A L k T} {g : T ⟶ T₀} {c : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c)
    (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt) : CommV θx' θy' g c := by
  intro T' t a z J hJ
  have e₀ := congrArg Additive.ofMul (h T' t a z J hJ)
  have e₁ := congrArg Additive.ofMul (ratio_const hG hA hL θx' θx hx t a ((t ≫ θy.pt) * a) hJ)
  have e₂ := congrArg Additive.ofMul (ratio_const hG hA hL θy' θy hy t a ((t ≫ θx.pt) * a) hJ)
  rw [hx, hy]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at e₀ e₁ e₂ ⊢
  linear_combination (norm := abel) e₀ + e₁ - e₂

theorem CommV.restrict (hL : L.IsLB) {T T₀ T₁ : Over S}
    {θx θy : ThetaGrp A L k T} {g : T ⟶ T₀} {c : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c) (f : T₁ ⟶ T) :
    ∃ θx₁ θy₁ : ThetaGrp A L k T₁, θx₁.pt = f ≫ θx.pt ∧ θy₁.pt = f ≫ θy.pt ∧ CommV θx₁ θy₁ (f ≫ g) c := by
  obtain ⟨θx₁, px, vx⟩ := exists_restrict hL θx f
  obtain ⟨θy₁, py, vy⟩ := exists_restrict hL θy f
  refine ⟨θx₁, θy₁, px, py, fun T' t a z J hJ => ?_⟩
  rw [vx _ _ _ _ _ hJ, vx _ _ _ _ _ hJ, vy _ _ _ _ _ hJ, vy _ _ _ _ _ hJ, px, py, ← Category.assoc,
    ← Category.assoc, ← Category.assoc]
  exact h T' (t ≫ f) a z J hJ

theorem CommV.mul [IsCommMonObj A] (hL : L.IsLB) {T T₀ : Over S}
    {θx θx' θy : ThetaGrp A L k T} {g : T ⟶ T₀} {c c' : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c)
    (h' : CommV θx' θy g c') : ∃ θ : ThetaGrp A L k T, θ.pt = θx.pt * θx'.pt ∧ CommV θ θy g (c * c') := by
  obtain ⟨θ, p, v⟩ := exists_mul hL θx θx'
  refine ⟨θ, p, fun T' t a z J hJ => ?_⟩
  have e₀ := congrArg Additive.ofMul (h T' t a z J hJ)
  have e₁ := congrArg Additive.ofMul (h' T' t ((t ≫ θx.pt) * a) z J hJ)
  rw [v _ _ _ _ _ hJ, v _ _ _ _ _ hJ, p, MonObj.comp_mul, map_mul, mul_comm (t ≫ θx.pt) (t ≫ θx'.pt),
    _root_.mul_assoc (t ≫ θx'.pt), mul_left_comm (t ≫ θx.pt) (t ≫ θy.pt)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at e₀ e₁ ⊢
  linear_combination (norm := abel) e₀ + e₁

theorem exists_commV_of_le (hL : L.IsLB) {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} {V W : T.left.Opens}
    (hle : W ≤ V)
    (h₁ : ∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y)
    (h₂ : ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
      CommIsOf A L k θx θy (unitRes V c)) :
    ∃ θx θy : ThetaGrp A L k (overRes W), θx.pt = overResι W ≫ x ∧ θy.pt = overResι W ≫ y ∧
      CommV θx θy (overResι W) c := by
  obtain ⟨θx, θy, px, py⟩ := h₁
  let f : overRes W ⟶ overRes V := Over.homMk (T.left.homOfLE hle) (by
    show T.left.homOfLE hle ≫ V.ι ≫ T.hom = W.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hf : f ≫ overResι V = overResι W := Over.OverMorphism.ext (T.left.homOfLE_ι hle)
  obtain ⟨θx₁, θy₁, qx, qy, hc⟩ := ((commIs_iff hL V θx θy c).1 (h₂ θx θy px py)).restrict hL f
  refine ⟨θx₁, θy₁, ?_, ?_, hf ▸ hc⟩
  · rw [qx, px, ← Category.assoc, hf]
  · rw [qy, py, ← Category.assoc, hf]

end GlobalTheory.WeilMul

namespace GlobalTheory

open WeilMul in

theorem weilIs_mul_left : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x x' y : T ⟶ P.A)
    (c c' : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k x' y c' →
      WeilIs P.A P.L k (x * x') y (c * c') := by
  intro hG S P k T x x' y c c' h h' p
  have := P.isAb.comm
  obtain ⟨V, hV, a₁, a₂⟩ := h p
  obtain ⟨V', hV', b₁, b₂⟩ := h' p
  obtain ⟨θx, θy, px, py, hc⟩ := exists_commV_of_le P.isLB (inf_le_left : V ⊓ V' ≤ V) a₁ a₂
  obtain ⟨θx', θy', px', py', hc'⟩ := exists_commV_of_le P.isLB (inf_le_right : V ⊓ V' ≤ V') b₁ b₂
  obtain ⟨θ, pθ, hθ⟩ := hc.mul P.isLB (hc'.congr hG P.isAb P.isLB rfl (py.trans py'.symm))
  have q : θ.pt = overResι (V ⊓ V') ≫ (x * x') := by rw [pθ, px, px', MonObj.comp_mul]
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ⟨θ, θy, q, py⟩, fun θ₁ θ₂ p₁ p₂ => ?_⟩
  exact (commIs_iff P.isLB _ _ _ _).2 (hθ.congr hG P.isAb P.isLB (p₁.trans q.symm) (p₂.trans py.symm))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_gen_of_local_on_base {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom)
    (h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = 1)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (p ⁻¹ᵁ U).ι ≫ φ k) ε), t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen := by
  have loc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : LB.Gen (LB.LinComb L (fun i => (p ⁻¹ᵁ U).ι ≫ φ i) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (b : Z ⟶ S) (z : Z) (J), Good L z J →
        r ≫ (p ⁻¹ᵁ U).ι = b ≫ e → val t r z J = 1 := by
    intro s
    obtain ⟨U, hs, t, ht⟩ := h s
    obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
        n ≫ (p ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ p ≫ e :=
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q (p y.1)) he
        exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := fun i => (p ⁻¹ᵁ U).ι ≫ φ i) (ε' := ε)
      (fun V _ k => by
        have q := h0 V (fun χ => k ((p ⁻¹ᵁ U).ι ≫ p ≫ χ))
        refine Eq.trans (DVR.prod_sum₂ (K := K) (K' := K) (U := V) _
          (c := ∏ i, k ((p ⁻¹ᵁ U).ι ≫ φ i) ^ ε i) rfl
          (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by
            show k (n ≫ _ ≫ _) ^ _ = _
            rw [← Category.assoc n, n₁]; simp only [Category.assoc]).trans q))) ?_
        simp)
      (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
    refine ⟨U, hs, t', ht', fun Z r b z J hJ hr => ?_⟩
    have : r ≫ n = r := by
      rw [← cancel_mono (p ⁻¹ᵁ U).ι, Category.assoc, n₁, ← Category.assoc, hr, Category.assoc,
        ← Category.assoc e, he, Category.id_comp]
    rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
  choose U hU t ht hn using loc
  have agree : ∀ (s s' : S) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U s).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ U s').toScheme) (z : Z) (J), Good L z J →
      r ≫ (p ⁻¹ᵁ U s).ι = r' ≫ (p ⁻¹ᵁ U s').ι → val (t s) r z J = val (t s') r' z J := by
    intro s s' Z r r' z J hJ hr
    let V : S.Opens := U s ⊓ U s'
    have mk : ∀ W : S.Opens, V ≤ W → ∃ m : pullback p V.ι ⟶ (p ⁻¹ᵁ W).toScheme,
        m ≫ (p ⁻¹ᵁ W).ι = pullback.fst p V.ι := fun W hW =>
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ W).ι (pullback.fst p V.ι) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q y) (pullback.condition (f := p) (g := V.ι))
        exact (congrArg (· ∈ W) e').mpr (hW (pullback.snd p V.ι y).2)), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨m, hm⟩ := mk (U s) inf_le_left
    obtain ⟨m', hm'⟩ := mk (U s') inf_le_right
    let e' : V.toScheme ⟶ pullback p V.ι := pullback.lift (V.ι ≫ e) (𝟙 _) (by simp [he])
    have he' : e' ≫ pullback.fst p V.ι = V.ι ≫ e := pullback.lift_fst _ _ _
    obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = (r ≫ (p ⁻¹ᵁ U s).ι) ≫ p :=
      ⟨IsOpenImmersion.lift V.ι ((r ≫ (p ⁻¹ᵁ U s).ι) ≫ p) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
    let ρ : Z ⟶ pullback p V.ι := pullback.lift (r ≫ (p ⁻¹ᵁ U s).ι) v hv.symm
    have hρ : ρ ≫ pullback.fst p V.ι = r ≫ (p ⁻¹ᵁ U s).ι := pullback.lift_fst _ _ _
    have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
    have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
    have key := gen_unique' hL (φ := fun i => m ≫ (p ⁻¹ᵁ U s).ι ≫ φ i) (ε := ε)
      (φ' := fun i => m' ≫ (p ⁻¹ᵁ U s').ι ≫ φ i) (ε' := ε)
      (fun W _ k => Finset.prod_congr rfl fun i _ => by
        show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
        rw [← Category.assoc, ← Category.assoc m, hm, hm'])
      (pullback.snd p V.ι) e' (pullback.lift_snd _ _ _) (hp V) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
      (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
        rw [val_pull hI, val_pull hI, hn s _ _ V.ι y I hI (by rw [Category.assoc, hm, he']),
          hn s' _ _ V.ι y I hI (by rw [Category.assoc, hm', he'])]) Z ρ z J hJ
    rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key
  obtain ⟨u, hu, -⟩ := glue_gen hL φ ε (fun s => p ⁻¹ᵁ U s) (fun y => ⟨p y, hU _⟩) t ht agree
  exact ⟨u, hu⟩

theorem exists_gen_zsmul {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (k : ℤ) :
    ∃ u : LB.Gen (LB.LinComb L φ (fun i => k * ε i)), u.IsGen := by
  refine ⟨⟨fun j => t.s j ^ k⟩, fun i j => ?_⟩
  have h := congrArg (· ^ k) (ht i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _))

theorem exists_gen_neg_of_sym (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Out.Sym A L) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), u.IsGen := by
  refine exists_gen_of_local_on_base hL _ _ A.hom η[A].left (Over.w η[A]) (fun V => surj_snd hG hA (Over.mk V.ι))
    (fun U _ h => ?_) (fun s => ?_)
  · have e : η[A].left ≫ (GrpObj.inv : A ⟶ A).left = η[A].left :=
      congrArg (fun q => q.left) (show η[A] ≫ (GrpObj.inv : A ⟶ A) = η[A] from GrpObj.one_inv)
    rw [Fin.prod_univ_two]
    show h (η[A].left ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) * h (η[A].left ≫ 𝟙 _) ^ (-1 : ℤ) = 1
    rw [e, Category.comp_id]; simp
  · obtain ⟨U, hU, t, ht⟩ := hs s
    obtain ⟨t', ht', -⟩ := exists_gen hL
      (φ' := fun k => (A.hom ⁻¹ᵁ U).ι ≫ (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) k) (ε' := ![1, -1])
      (fun V _ h => by simp [Fin.prod_univ_two]) t ht
    exact ⟨U, hU, t', ht'⟩

theorem exists_gen_negLB : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S),
    ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen := by
  intro hG S P k T
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG P.isAb P.isLB P.sym
  obtain ⟨w, hw⟩ := exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hu (snd T P.A).left) (-k)
  obtain ⟨t, ht, -⟩ := exists_gen P.isLB (K' := Fin 2)
    (φ' := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) (ε' := ![k, -k])
    (fun V _ h => by simp [Fin.prod_univ_two, mul_comm]) w hw
  exact ⟨t, ht⟩

end GlobalTheory
end
end

