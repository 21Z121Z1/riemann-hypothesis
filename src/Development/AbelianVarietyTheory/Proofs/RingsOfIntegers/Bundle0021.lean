import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SquareRes
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

variable {B B' G G' T T' S₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {j : ℕ}
  {pr : Fin j → (B' ⟶ B)} {prG : Fin j → (G' ⟶ G)} {p : T ⟶ B} {p' : T' ⟶ B'} {f : T ⟶ G} {f' : T' ⟶ G'}

private theorem sec_res_comp_algebraMap {X : Scheme.{0}} {U V W : X.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (x : Γ(X, W)ˣ) : res h₁ (res h₂ x) = res (h₁.trans h₂) x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private theorem res_self_lemma {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have e : homOfLE h = 𝟙 U := rfl
  rw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

private theorem linComb_comp_U_le_linComb_linComb_U {eG' : S₀ ⟶ G'} (jN : Fin j → L.ι) :
    (LB.LinComb L (fun i => eG' ≫ prG i) (fun _ => 1)).U jN ≤
      (LB.LinComb (LB.LinComb L prG (fun _ => 1)) (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jN) := by
  intro x hx
  simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
    SetLike.mem_coe] at hx ⊢
  intro _ k
  simpa using hx k

private theorem linComb_unit_U_le {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).U (fun _ => a) ⊓
      (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).U (fun _ => b) ≤ e ⁻¹ᵁ (N.U a ⊓ N.U b) := by
  intro x hx
  simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
    SetLike.mem_coe, Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_inf] at hx ⊢
  exact ⟨hx.1 PUnit.unit, hx.2 PUnit.unit⟩

private theorem linComb_unit_g_eq {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (LB.LinComb N (K := PUnit) (fun _ => e) (fun _ => 1)).g (fun _ => a) (fun _ => b) =
      res (linComb_unit_U_le N e a b) (pullU e (N.U a ⊓ N.U b) (N.g a b)) := by
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one, pow_one]
  rfl

private theorem res_pullU_id_eq_res'' {X : Scheme.{0}} {U V : X.Opens} (x : Γ(X, U)ˣ) (h : V ≤ (𝟙 X) ⁻¹ᵁ U) :
    res h (pullU (𝟙 X) U x) = res (fun y hy => h hy) x := by
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl

private theorem res_congr_of_index_eq {X : Scheme.{0}} {Idx : Type*} {U : Idx → X.Opens} (s : ∀ a, Γ(X, U a)ˣ) {V : X.Opens}
    {a b : Idx} (e : a = b) (h₁ : V ≤ U a) (h₂ : V ≤ U b) : res h₁ (s a) = res h₂ (s b) := by
  subst e
  rfl

theorem idIso_rig (hL : L.IsLB) {eG : S₀ ⟶ G} {eG' : S₀ ⟶ G'} (rL : LB.Gen (L.pull eG))
    (hG : ∀ (i : Fin j) (_ : PUnit), eG' ≫ prG i = 𝟙 S₀ ≫ eG)
    (hr : (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)).IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := Fin j) (fun i => eG' ≫ prG i) (fun _ => 1)),
      GeneratorPullback.MapsAt L (LB.LinComb L prG (fun _ => 1)) prG (idIso _) eG' 1
        (GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
          (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)) b ∧
      LB.Gen.Corr L _ _ _ _ b (GeneratorPullback.finProdGen L (J := Fin j) (fun _ _ => eG) (fun _ _ => 1) (fun _ => rL)) := by
  refine ⟨⟨fun jN => res (linComb_comp_U_le_linComb_linComb_U (prG := prG) (eG' := eG') jN) ((GeneratorPullback.boxGen L prG (fun _ : PUnit => eG') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (prG i) (𝟙 S₀) (fun _ => eG) (fun _ => 1) (fun _ => eG') (hG i) rL)).s fun _ => jN)⟩, ?_, ?_⟩
  · unfold GeneratorPullback.MapsAt
    intro jN jL
    have H := hr (fun _ => jN) (fun _ => jL)
    have hO : eG' ⁻¹ᵁ ((L.LinComb prG fun _ => 1).U jN ⊓ (L.LinComb prG fun _ => 1).U jL) ≤
        ((L.LinComb prG fun _ => 1).LinComb (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jN) ⊓
          ((L.LinComb prG fun _ => 1).LinComb (K := PUnit) (fun _ => eG') (fun _ => 1)).U (fun _ => jL) := by
      intro x hx
      simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
        SetLike.mem_coe, Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_inf] at hx ⊢
      exact ⟨fun _ => hx.1, fun _ => hx.2⟩
    have H2 := congrArg (res hO) H
    erw [linComb_unit_g_eq] at H2
    simp only [map_mul, sec_res_comp_algebraMap, res_self_lemma] at H2
    dsimp only
    erw [sec_res_comp_algebraMap]
    simp only [pow_one, zpow_one]
    exact H2
  · unfold LB.Gen.Corr GeneratorPullback.finProdGen
    intro j₁ j' c₁ c₂ hj
    have hk : ∀ k, j₁ k = j' (k, PUnit.unit) := fun k => hj k (k, PUnit.unit) (by simpa using hG k PUnit.unit)
    clear hj c₁ c₂ hr
    dsimp only
    unfold GeneratorPullback.boxGen GeneratorPullback.pullAlong
    dsimp only
    erw [sec_res_comp_algebraMap, map_prod, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    erw [sec_res_comp_algebraMap]
    exact (sec_res_comp_algebraMap _ _ _).trans ((res_pullU_id_eq_res'' _ _).trans
      ((res_congr_of_index_eq rL.s (funext fun k => by cases k; exact hk i) _ _).trans (sec_res_comp_algebraMap _ _ _).symm))

private theorem pullU_res_eq_res_pullU'' {X Y : Scheme.{0}} (r : Y ⟶ X) {U U' : X.Opens} (h' : U' ≤ U)
    (hh : r ⁻¹ᵁ U' ≤ r ⁻¹ᵁ U) (x : Γ(X, U)ˣ) : pullU r U' (res h' x) = res hh (pullU r U x) := by
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

private theorem div_g_eq_res_mul_res_inv {X : Scheme.{0}} (A B : LB X) (p q : A.ι × B.ι) :
    (A.div B).g p q = res (inf_le_inf inf_le_left inf_le_left) (A.g p.1 q.1) *
      (res (inf_le_inf inf_le_right inf_le_right) (B.g p.2 q.2))⁻¹ := rfl

private theorem pull_g_eq_res_pullU {X Y : Scheme.{0}} (N : LB X) (e : Y ⟶ X) (a b : N.ι) :
    (N.pull e).g (fun _ => a) (fun _ => b) = res (linComb_unit_U_le N e a b) (pullU e (N.U a ⊓ N.U b) (N.g a b)) :=
  linComb_unit_g_eq N e a b

private theorem res_mul_rings_of_integers {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a b : Γ(X, U)ˣ) :
    res h (a * b) = res h a * res h b := map_mul _ _ _

private theorem res_inv' {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    res h a⁻¹ = (res h a)⁻¹ := map_inv _ _

private theorem toFld_gm_res {X Y : Scheme.{0}} (r : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hV : V ≤ r ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) (y : Y) (hy : y ∈ V) : gm (𝟙 Y) y V (res hV (pullU r U u)) = gm r y U u := by
  have hy' : r y ∈ U := hV hy
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  unfold gm
  rw [dif_pos hy1, dif_pos hy']
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, pullU]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hV) y hy _

private theorem gm_id_res_eq' {Y : Scheme.{0}} {U V : Y.Opens} (hV : V ≤ U) (u : Γ(Y, U)ˣ) (y : Y) (hy : y ∈ V) :
    gm (𝟙 Y) y V (res hV u) = gm (𝟙 Y) y U u := by
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  have hy2 : (𝟙 Y : Y ⟶ Y) y ∈ U := hV hy
  unfold gm
  rw [dif_pos hy1, dif_pos hy2]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, res, pullU]
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hV) y hy _

private theorem units_ext_of_gm_id_eq' {Y : Scheme.{0}} {V : Y.Opens} (a b : Γ(Y, V)ˣ)
    (H : ∀ y (hy : y ∈ V), gm (𝟙 Y) y V a = gm (𝟙 Y) y V b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext Y.sheaf V
  intro y hy
  have e := congrArg Units.val (H y hy)
  have hy1 : (𝟙 Y : Y ⟶ Y) y ∈ V := hy
  unfold gm at e
  rw [dif_pos hy1] at e
  exact e

theorem square_res (hM' : M'.IsLB)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {we : LB.Iso (L.pull f) (M.pull p)}
    {we' : LB.Iso ((LB.LinComb L prG (fun _ => 1)).pull f') (M'.pull p')} {h : Fin j → (T' ⟶ T)}
    (hwe : we'.IsGen) (Q : BoxSquare w we we' h) (jNM : Fin j → M.ι) (jM' : M'.ι) (jL' jNL : Fin j → L.ι)
    (V : T'.Opens) (h₁ : V ≤ p' ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (jNM, jM'))
    (h₂ : V ≤ (LB.div (M'.pull p') ((LB.LinComb L prG (fun _ => 1)).pull f')).U (fun _ => jM', fun _ => jL'))
    (h₃ : ∀ i, V ≤ h i ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (fun _ => jNM i, fun _ => jNL i))
    (h₄ : V ≤ f' ⁻¹ᵁ (LB.div (LB.LinComb L prG (fun _ => 1)) (LB.LinComb L prG (fun _ => 1))).U (jNL, jL')) :
    res h₁ (pullU p' _ (w.s (jNM, jM'))) * res h₂ (we'.s (fun _ => jM', fun _ => jL')) =
      (∏ i, res (h₃ i) (pullU (h i) _ (we.s (fun _ => jNM i, fun _ => jNL i)))) *
        res h₄ (pullU f' _ ((idIso (LB.LinComb L prG (fun _ => 1))).s (jNL, jL'))) := by
  have hw2 := hwe
  unfold LB.Gen.IsGen at hw2
  have hV1 : V ≤ ((M'.pull p').div ((L.LinComb prG fun _ => 1).pull f')).U (fun _ => jM', fun _ => jNL) ⊓
      ((M'.pull p').div ((L.LinComb prG fun _ => 1).pull f')).U (fun _ => jM', fun _ => jL') := by
    intro x hx
    have a2 := h₂ hx
    have a4 := h₄ hx
    clear h₁ h₃ Q hwe hw2 h₂ h₄ hx
    simp only [LB.div, LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
      TopologicalSpace.Opens.coe_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.mem_preimage, Set.mem_inter_iff] at a2 a4 ⊢
    refine ⟨⟨a2.1, ?_⟩, a2.1, ?_⟩
    · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => a4.1 k
    · exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => a4.2 k
  have hg := congrArg (res hV1) (hw2 (fun _ => jM', fun _ => jNL) (fun _ => jM', fun _ => jL'))
  simp only [map_mul, sec_res_comp_algebraMap] at hg
  rw [div_g_eq_res_mul_res_inv] at hg
  dsimp only at hg
  rw [pull_g_eq_res_pullU] at hg
  erw [pull_g_eq_res_pullU] at hg
  simp only [map_mul, map_inv, sec_res_comp_algebraMap] at hg
  have hVp : V ≤ p' ⁻¹ᵁ M'.U jM' := fun y hy => (h₁ hy).2
  have hself : ∀ (k : V ≤ p' ⁻¹ᵁ (M'.U jM' ⊓ M'.U jM')),
      res k (pullU p' (M'.U jM' ⊓ M'.U jM') (M'.g jM' jM')) = 1 := by
    intro k
    have e1 := pullU_res_eq_res_pullU'' p' (le_inf le_rfl le_rfl : M'.U jM' ≤ M'.U jM' ⊓ M'.U jM') (fun y hy => ⟨hy, hy⟩)
      (M'.g jM' jM')
    rw [hM'.g_self jM', map_one] at e1
    exact (sec_res_comp_algebraMap hVp (show p' ⁻¹ᵁ M'.U jM' ≤ p' ⁻¹ᵁ (M'.U jM' ⊓ M'.U jM') from fun y hy => ⟨hy, hy⟩) _).symm.trans
      (by rw [← e1, map_one])
  have hX : ∀ k, res hV1 (res k (pullU p' (M'.U jM' ⊓ M'.U jM') (M'.g jM' jM'))) = 1 :=
    fun k => (sec_res_comp_algebraMap _ _ _).trans (hself _)
  erw [res_mul_rings_of_integers, res_inv'] at hg
  erw [hX] at hg
  rw [_root_.one_mul, eq_inv_mul_iff_mul_eq] at hg
  rw [← hg]
  refine (mul_left_comm _ _ _).trans ((mul_comm _ _).trans ?_)
  refine congrArg₂ (· * ·) ?_ ((sec_res_comp_algebraMap _ _ _).trans rfl)
  apply units_ext_of_gm_id_eq'
  intro y hy
  have c1 : ∀ i, pr i (p' ((𝟙 T' : T' ⟶ T') y)) ∈ M.U (jNM i) := fun i => Set.mem_iInter.1 (h₁ hy).1 i
  have c2 : p' ((𝟙 T' : T' ⟶ T') y) ∈ M'.U jM' := (h₁ hy).2
  have c3 : ∀ i, prG i (f' ((𝟙 T' : T' ⟶ T') y)) ∈ L.U (jNL i) := fun i => Set.mem_iInter.1 (h₄ hy).1 i
  have q := Q T' (𝟙 T') y jNM jM' jNL c1 c2 c3
  simp only [bw, Geo.Tor.gw, Category.id_comp] at q
  rw [map_mul, map_prod, toFld_gm_res _ _ _ _ hy, gm_id_res_eq' _ _ _ hy,
    Finset.prod_congr rfl (fun i _ => toFld_gm_res (h i) (h₃ i) _ y hy)]
  exact q

end GlobalTheory.PowUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TauBalBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}

theorem tau_val (D : DegPre R) {Z : Scheme.{0}} {y : Z} {J} (hJ : Good D.P.L y J) (p q : D.X) (r : Z ⟶ (TK R).left) :
    val (D.tau p q) r y J = val (D.psi (p + q)) r y J * (val (D.psi p) r y J)⁻¹ * (val (D.psi q) r y J)⁻¹ *
      (val D.rigK r y J)⁻¹ := by
  unfold DegPre.tau
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]

private theorem inv_mul_mul_mul_inv_mul_eq_commGroup {G : Type*} [CommGroup G] (A B C E a b c e : G) :
    A⁻¹ * B * C * E⁻¹ * (a * b⁻¹ * c⁻¹ * e⁻¹) = A⁻¹ * a * (B⁻¹ * b)⁻¹ * (C⁻¹ * c)⁻¹ * (E * e)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tau_box (pD : IsPowDeg D' D j) {y : (TK R).left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (p q : D'.X) :
    ((om pD.w y J J' (cP D' (TK R) p * cP D' (TK R) q).left)⁻¹ * om pD.w y J J' (cP D' (TK R) p).left *
      om pD.w y J J' (cP D' (TK R) q).left *
      (om pD.w y J J' (𝟙 _ ≫ (toUnit (TK R)).left ≫ eSec D'.P.A))⁻¹) * val (D'.tau p q) (𝟙 _) y J' =
      ∏ i, val (D.tau (pD.xe p i) (pD.xe q i)) (𝟙 _) y J := by
  have hc : ∀ x : D'.X, 𝟙 _ ≫ D'.xK x = (cP D' (TK R) x).left := fun x => by
    simp only [Category.id_comp, DegPre.xK, ptK, cP]
  have hpq : cP D' (TK R) (p + q) = cP D' (TK R) p * cP D' (TK R) q := by
    unfold cP
    rw [D'.c_add, padd, comp_lift_assoc]
    rfl
  have h1 := psi_val pD hJ hJ' (p + q) (𝟙 _)
  have h2 := psi_val pD hJ hJ' p (𝟙 _)
  have h3 := psi_val pD hJ hJ' q (𝟙 _)
  have h4 := rig_val pD hJ hJ' (𝟙 _)
  rw [hc, hpq] at h1
  rw [hc] at h2 h3
  have e : ∀ i, val (D.tau (pD.xe p i) (pD.xe q i)) (𝟙 _) y J =
      val (D.psi (pD.xe (p + q) i)) (𝟙 _) y J * (val (D.psi (pD.xe p i)) (𝟙 _) y J)⁻¹ *
        (val (D.psi (pD.xe q i)) (𝟙 _) y J)⁻¹ * (val D.rigK (𝟙 _) y J)⁻¹ := fun i => by
    rw [tau_val D hJ, map_add, Pi.add_apply]
  rw [Finset.prod_congr rfl (fun i _ => e i), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib, ← h1, ← h2,
    ← h3, ← h4, tau_val D' hJ' p q (𝟙 _)]
  exact inv_mul_mul_mul_inv_mul_eq_commGroup _ _ _ _ _ _ _ _

theorem rosatiφ_pr {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (π : A' ⟶ A) [IsMonHom π] {f g : A ⟶ A} {f' g' : A' ⟶ A'} (hf : f' ≫ π = π ≫ f) (hg : g' ≫ π = π ≫ g)
    (a : Fin 6) : rosatiφ A' f' g' a ≫ π.left = (π ⊗ₘ π).left ≫ rosatiφ A f g a := by
  fin_cases a <;>
    simp [rosatiφ, padd, ← Over.comp_left, comp_lift_assoc, IsMonHom.mul_hom, lift_map_assoc, hf, hg,
      tensorHom_fst_assoc, tensorHom_snd_assoc, tensorHom_fst, tensorHom_snd]

private theorem mul_eq_of_four_relations_commGroup {G : Type*} [CommGroup G] (X1 X2 X3 X4 LinearSubstitution X6 Eo t1 t2 U P1 P2 PU : G)
    (hT1 : X1⁻¹ * X2 * X3 * Eo⁻¹ * t1 = P1) (hT2 : X4⁻¹ * LinearSubstitution * X6 * Eo⁻¹ * t2 = P2)
    (hBU : X1 * X2⁻¹ * X3⁻¹ * X4⁻¹ * LinearSubstitution * X6 * U = PU) (hB : P1 * PU = P2) : t1 * U = t2 := by
  subst hT1 hBU hB
  apply mul_left_cancel (a := X4⁻¹ * LinearSubstitution * X6 * Eo⁻¹)
  rw [hT2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem mul_inv_inv_inv_mul_mul_eq_one {G : Type*} [CommGroup G] (x : G) : x * x⁻¹ * x⁻¹ * x⁻¹ * x * x = 1 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem tauBal_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g → IsMonHom f' → IsMonHom g' → (∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) → (∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g) → RosatiAdj D.P.A D.P.L f g → ∀ (a a' : D.X → D.X) (b b' : D'.X → D'.X), (∀ x i, pD.xe (b x) i = a (pD.xe x i)) → (∀ x i, pD.xe (b' x) i = a' (pD.xe x i)) → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (a' y) = D.c y ≫ g) → D.TauBal f g a a' → D'.TauBal f' g' b b' := by
  intro hG R _ _ j D D' pD f g f' g' hfm hgm hfm' hgm' hf hg hr a a' b b' hb hb' ca ca' hB
  have hcb : ∀ x, cP D' (TK R) x ≫ f' = cP D' (TK R) (b x) := fun x => by
    unfold cP
    rw [Category.assoc]
    congr 1
    refine pD.pw.lim.hom_ext (fun k => ?_)
    rcases k with ⟨i⟩
    simp only [Fan.mk_π_app, Category.assoc, hf i, pD.c_pr, ← reassoc_of% (pD.c_pr x i), hb, ca]
  have hcb' : ∀ x, cP D' (TK R) x ≫ g' = cP D' (TK R) (b' x) := fun x => by
    unfold cP
    rw [Category.assoc]
    congr 1
    refine pD.pw.lim.hom_ext (fun k => ?_)
    rcases k with ⟨i⟩
    simp only [Fan.mk_π_app, Category.assoc, hg i, pD.c_pr, ← reassoc_of% (pD.c_pr x i), hb', ca']
  unfold DegPre.TauBal
  intro u' hu' h0' y y'
  obtain ⟨u, hu, h0⟩ := exists_ros hG D.P.isAb D.P.isLB f g hr
  apply corr_of_val D'.P.isLB
  intro z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have T1 := tau_box pD hJ hJ' (b y) y'
  have T2 := tau_box pD hJ hJ' y (b' y')
  have HB : ∀ i, val (D.tau (pD.xe (b y) i) (pD.xe y' i)) (𝟙 _) z J *
      val u (D.pt2 (pD.xe y i) (pD.xe y' i)) z J = val (D.tau (pD.xe y i) (pD.xe (b' y') i)) (𝟙 _) z J := fun i => by
    rw [hb, hb']
    have := val_corr hJ (hB u hu h0 (pD.xe y i) (pD.xe y' i)) (𝟙 _)
    rwa [val_mul hJ, val_pull hJ, Category.id_comp] at this
  have hpt : ∀ i, D'.pt2 y y' ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left = D.pt2 (pD.xe y i) (pD.xe y' i) := fun i => by
    show (lift (cP D' (TK R) y) (cP D' (TK R) y')).left ≫ _ = (lift (cP D (TK R) _) (cP D (TK R) _)).left
    rw [← Over.comp_left, lift_map, cPoint_pr pD, cPoint_pr pD]
  have hψ : ∀ i k, rosatiφ D'.P.A f' g' k ≫ (pD.pw.pr i).left =
      (pD.pw.pr i ⊗ₘ pD.pw.pr i).left ≫ rosatiφ D.P.A f g k := fun i k => by
    have := pD.pw.hom i
    exact rosatiφ_pr (pD.pw.pr i) (hf i) (hg i) k
  have hp : Function.Surjective (D'.P.A ⊗ D'.P.A).hom.appTop.hom := by
    have h1 := surj_comp (surj_snd hG D'.P.isAb D'.P.A) (hG _ D'.P.A D'.P.isAb).2
    rwa [Over.w] at h1
  have hone : ∀ {Z : Scheme.{0}} (z₀ : Z) (J₀ : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z₀ J₀ → ∀ (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left), val u' (r ≫ zero2 D'.P.A) z₀ J₀ = 1 := by
    intro Z z₀ J₀ hJ₀ r
    have := val_corr hJ₀ h0' r
    rwa [val_pull hJ₀, val_one] at this
  have hcond : ∀ (y₀ : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J₀ J₀', Good D.P.L y₀ J₀ → Good D'.P.L y₀ J₀' →
      (∏ k, bw pD.w (zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k) y₀
        (fun i => J₀ ((zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k) ≫ (pD.pw.pr i).left))
        (J₀' (zero2 D'.P.A ≫ rosatiφ D'.P.A f' g' k)) ^ rosatiε k) * val u' (zero2 D'.P.A) y₀ J₀' =
      ∏ i, val u (zero2 D'.P.A ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left) y₀ J₀ := by
    intro y₀ J₀ J₀' hJ₀ hJ₀'
    have hz : ∀ i, zero2 D'.P.A ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i).left = 𝟙 _ ≫ zero2 D.P.A := fun i => by
      have := pD.pw.hom i
      rw [Category.id_comp]
      unfold zero2
      rw [← Over.comp_left, lift_map, IsMonHom.one_hom]
    have hz' := hone y₀ J₀' hJ₀' (𝟙 _)
    rw [Category.id_comp] at hz'
    have hu0 : val u (𝟙 _ ≫ zero2 D.P.A) y₀ J₀ = 1 := by
      have := val_corr hJ₀ h0 (𝟙 _)
      rwa [val_pull hJ₀, val_one] at this
    simp only [hz, hu0, Finset.prod_const_one, hz', _root_.mul_one]
    have PR0 := prod_ros f' g' (η[D'.P.A]) (η[D'.P.A]) (fun ψ => om pD.w y₀ J₀ J₀' ψ)
    beta_reduce at PR0
    have e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = η[D'.P.A] := by
      show toUnit _ ≫ η[D'.P.A] = η[D'.P.A]
      rw [toUnit_unit, Category.id_comp]
    have e2 : η[D'.P.A] * η[D'.P.A] = η[D'.P.A] := by rw [← e1, _root_.mul_one]
    rw [IsMonHom.one_hom, IsMonHom.one_hom, e2] at PR0
    exact PR0.trans (mul_inv_inv_inv_mul_mul_eq_one _)
  have BU := CubBox.box_unique D.P.isLB D'.P.isLB pD.w pD.w_gen hψ hu' hu ((D'.P.A ⊗ D'.P.A).hom) (zero2 D'.P.A)
    (by unfold zero2; exact Over.w (lift η[D'.P.A] η[D'.P.A])) hp hcond (TK R).left (D'.pt2 y y') z J J' hJ hJ'
  simp only [hpt] at BU
  have BU2 : (∏ k, om pD.w z J J' ((lift (cP D' (TK R) y) (cP D' (TK R) y')).left ≫ rosatiφ D'.P.A f' g' k) ^
      rosatiε k) * val u' (D'.pt2 y y') z J' = ∏ i, val u (D.pt2 (pD.xe y i) (pD.xe y' i)) z J := BU
  have PR := prod_ros f' g' (cP D' (TK R) y) (cP D' (TK R) y') (fun ψ => om pD.w z J J' ψ)
  beta_reduce at PR
  rw [hcb, hcb'] at PR
  rw [PR] at BU2
  exact mul_eq_of_four_relations_commGroup _ _ _ _ _ _ _ _ _ _ _ _ _ T1 T2 BU2
    (by rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _ => HB i))

end GlobalTheory.TauBalBox
end
end

