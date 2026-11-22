import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0112

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAlgebraizationGroupOperationsCdvrStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraization_group_operations_cdvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) := by
  first | exact @GlobalTheory.GrpAlg.exists_group_operations | exact GlobalTheory.GrpAlg.exists_group_operations | (intros; apply GlobalTheory.GrpAlg.exists_group_operations <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegrees
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.InducingAut

open GlobalTheory.FieldBaseChange

theorem exists_const_ratio {K : Type} [CommRing K] {Y : Scheme.{0}} {N : LB Y} (hN : ∀ y : Y, ∃ i, y ∈ N.U i)
    (p : Y ⟶ Spec (CommRingCat.of K)) (hp : Function.Surjective p.appTop.hom)
    {t₁ t₂ : LB.Gen N} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen) :
    ∃ c : K, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : N.ι), r z ∈ N.U i →
      (gm r z (N.U i) (t₁.s i)).val = constVal (r ≫ p) z c * (gm r z (N.U i) (t₂.s i)).val := by
  have tr : ∀ {t : LB.Gen N}, t.IsGen → ∀ (i j : N.ι) (x : Y), x ∈ N.U i ⊓ N.U j →
      gm (𝟙 Y) x (N.U i) (t.s i) = gm (𝟙 Y) x (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) x (N.U j) (t.s j) := by
    intro t ht i j x hx
    have := congrArg (gm (𝟙 Y) x (N.U i ⊓ N.U j)) (ht i j)
    rwa [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  obtain ⟨u, hu⟩ := glue_unit ⊤ N.U (fun _ => le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hN y))
    (fun i => t₁.s i * (t₂.s i)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, tr h₁ i j x hx, tr h₂ i j x hx, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨a, ha⟩ := hp u.val
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, fun Z r z i hi => ?_⟩
  have key : (gm r z (N.U i) (t₁.s i) * (gm r z (N.U i) (t₂.s i))⁻¹).val = constVal (r ≫ p) z c := by
    rw [← map_inv, ← map_mul, ← hu i, gm_res r z _ hi]
    exact (gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial _))
  rw [← key, ← Units.val_mul, inv_mul_cancel_right]

theorem constVal_pow {K : Type} [CommRing K] {Z : Scheme.{0}} (π : Z ⟶ Spec (CommRingCat.of K)) (z : Z) (c : K)
    (k : ℕ) : constVal π z (c ^ k) = constVal π z c ^ k := by
  simp only [constVal, gs_eq π z ⊤ trivial, map_pow]

theorem isoRelM_change {Y Y' X₁ X₂ Z₁ Z₂ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w w' : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
    {g₂ : Z₂ ⟶ X₂} {h₂ : Y' ⟶ Z₂}
    {S : Type} [CommRing S] {π₁ : Z₁ ⟶ Spec (CommRingCat.of S)} (c : S)
    (hc : ∀ (y : Y') i₂ i₁, f₂ (m y) ∈ L₂.U i₂ → f₁ (m y) ∈ L₁.U i₁ →
      (isoVal w' (𝟙 Y' ≫ m) y i₂ i₁).val =
        constVal ((𝟙 Y' ≫ h₁) ≫ π₁) y c * (isoVal w (𝟙 Y' ≫ m) y i₂ i₁).val)
    {a : SecOver π₁ (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ)))}
    {b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))}
    (h : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w' m k g₁ h₁ a g₂ h₂ b) :
    GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g₁ h₁ (c ^ k • a : SecOver π₁ _) g₂ h₂ b := by
  refine (isoRelM_iff w m k h₁ h.1 _ h.2.1 _ _).2 fun y i₂ i₁ a₂ a₁ => ?_
  have b₁ : g₁ ((𝟙 Y' ≫ h₁) y) ∈ L₁.U i₁ :=
    (congrArg (fun q : Y' ⟶ X₁ => q y) h.1 : g₁ (h₁ y) = f₁ (m y)).symm ▸ a₁
  rw [powVal_smul _ _ _ y b₁, (isoRelM_iff w' m k h₁ h.1 _ h.2.1 _ _).1 h _ (𝟙 _) y i₂ i₁ a₂ a₁,
    zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hc y i₂ i₁ a₂ a₁,
    constVal_pow]
  ring

theorem mul_chart_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (g : Y ⟶ X) {a b c : ℤ}
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => a)))
    (s' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => b)))
    (s'' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => g) (fun _ => c))) :
    (∀ j, @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s''.f j) =
      @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s.f j) * @id Γ(Y, LB.wchart L (fun _ : Fin 1 => g) j) (s'.f j)) ↔
    ∀ y J, Good L y J → sval s'' (𝟙 Y) y J = sval s (𝟙 Y) y J * sval s' (𝟙 Y) y J := by
  constructor
  · intro h y J hJ
    exact (congrArg (gs (𝟙 Y) y _) (h _)).trans (gs_mul _ y _ (hJ.mem (fun _ : Fin 1 => g) (𝟙 Y)) _ _)
  · intro h j
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : Fin 1 => 𝟙 Y ≫ g) j
      (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
    have := h y J hJ
    rw [sval_of s _ y J j e, sval_of s' _ y J j e, sval_of s'' _ y J j e] at this
    exact this.trans (gs_mul _ y _ hy _ _).symm

section Frames

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_frame (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : ∃ w : Frm D F k b, w.IsGen :=
  exists_gen_of_local (V := F) D.P.L D.P.isLB _ _

variable {D F} in

theorem exists_frame_pow {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F k b) (hw : w.IsGen) (n : ℕ) :
    ∃ ω : Frm D F (k * n) b, ω.IsGen ∧ ∀ z J, Good D.P.L z J → val ω (𝟙 _) z J = val w (𝟙 _) z J ^ n := by
  obtain ⟨ω, h, v⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε (k * n))
    (fun U _ h => Finset.prod_congr rfl fun i _ => congrArg _ (by
      fin_cases i <;> simp [DegPre.lineε, mul_comm]))
    (GeneratorPullback.powGen D.P.L _ _ w n) (powGen_isGen _ _ _ w hw n)
  exact ⟨ω, h, fun z J hJ => (v _ _ z J hJ).trans (map_pow _ _ _)⟩

end Frames

section Unif

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem expandsF_change (hG : GlobalFnsSt) (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) {w w' : W0 U} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, ∀ (t : SecOver (abelianBase A F) (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Fam D.toPre F k),
      U.ExpandsF F k w' t s → U.ExpandsF F k w (c • t : SecOver (abelianBase A F) _) s := by
  have : IsIso U.gen.hom.left := ⟨⟨U.gen.inv.left, by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]⟩⟩
  have hp : Function.Surjective (U.gen.hom.left ≫ A.A.hom).appTop.hom := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    have : IsIso U.gen.hom.left.appTop := inferInstanceAs (IsIso (U.gen.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso U.gen.hom.left.appTop).2.comp (hG _ _ A.isAb).2
  obtain ⟨c, hc⟩ := exists_const_ratio (K := FractionRing R) (fun y => by
    obtain ⟨i, hi⟩ := exists_chart A.isLB (U.gen.hom.left y)
    obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (pullback.fst G.hom (jK R) y)
    exact ⟨(fun _ => j, fun _ => i), mem_pull.2 hj, mem_pull.2 hi⟩) (U.gen.hom.left ≫ A.A.hom) hp hw' hw
  refine ⟨algebraMap (FractionRing R) F c ^ k, ?_⟩
  rintro t s ⟨v, a, b⟩
  refine ⟨v, isoRelM_change (π₁ := abelianBase A F) _ (fun y i₂ i₁ a₂ a₁ => ?_) a, b⟩
  refine (hc _ _ y (fun _ => i₂, fun _ => i₁) ⟨mem_pull.2 a₂, mem_pull.2 a₁⟩).trans (congrArg (· * _) ?_)
  refine Eq.trans (congrArg (fun q => constVal q y c) ?_) (constVal_specMap _ (algebraMap (FractionRing R) F) y c)
  have hπ : (U.genF F).left ≫ abelianBase A F = groupBase G F :=
    congrArg (fun q => q.left) (lift_fst _ _ : U.genF F ≫ fst _ _ = _)
  have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  simp only [Category.id_comp]
  rw [hπ, e]
  exact (isPullback_groupBase F).w

theorem exists_transport (hG : GlobalFnsSt) (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {N : ℕ} (hN : 1 ≤ N) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) (Φ : Fam D.toPre F N →ₗ[F] Fam D.toPre F N)
    (hΦ : Function.Bijective Φ) :
    ∃ Ψ : SecA A F N ≃ SecA A F N,
      (∀ (s s' s'' : SecA A F N) (c : Γ((TFK (R := R) F).left, ⊤)),
        (∀ j, s''.f j = liftFun A.A _ c * s.f j + s'.f j) →
          ∀ j, (Ψ s'').f j = liftFun A.A _ c * (Ψ s).f j + (Ψ s').f j) ∧
      (∀ t, ∃ s, U.ExpandsF F N w₀ t s ∧ U.ExpandsF F N w₀ (Ψ t) (Φ s)) ∧
      ∀ w₁ : W0 U.toUnifPre, w₁.IsGen → ∀ t s s', U.ExpandsF F N w₁ t s → U.ExpandsF F N w₁ (Ψ t) s' →
        s' = Φ s := by
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
  let Ψ := (e.trans (LinearEquiv.ofBijective Φ hΦ)).trans e.symm
  have hΨ : ∀ t, e (Ψ t) = Φ (e t) := fun t => e.apply_symm_apply _
  refine ⟨Ψ.toEquiv, fun s s' s'' c h j => ?_, fun t => ⟨e t, (he _ _).2 rfl, (he _ _).2 (hΨ t)⟩,
    fun w₁ hw₁ t s s' h h' => ?_⟩
  · obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 c
    let t : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s
    let t' : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s'
    let t'' : SecOver (abelianBase A F) (LPow A.A A.L (N : ℤ) (TFK (R := R) F)) := s''
    have e₁ : t'' = c • t + t' := SecOver.ext _ _ fun j => (h j).trans rfl
    have e₂ : Ψ t'' = c • Ψ t + Ψ t' := by rw [e₁, map_add, map_smul]
    exact (congrArg (chartFun _ _ j) e₂).trans rfl
  · obtain ⟨c, hc⟩ := expandsF_change hG U.toUnifPre F N hw₀ hw₁
    have a := (he _ _).1 (hc t s h)
    have a' := (he _ _).1 (hc (Ψ t) s' h')
    exact a'.symm.trans ((e.map_smul c _).trans ((congrArg (c • ·) (hΨ t)).trans
      ((Φ.map_smul c _).symm.trans (congrArg Φ ((e.map_smul c t).symm.trans a)))))

end Unif

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem exists_qk_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k) (n : ℕ) :
    ∃ h : GtPtF D F, GtPtF.IsNsmul (k * n) p.g h ∧ GtPtF.IsIota (n • p.y) h :=
  (GlobalTheory.TorusExt.qkMk hB (k := k * n) (n • p.y) p.g (by
    rw [map_nsmul, ← GlobalTheory.TorusExt.qk_nsmul hB p, mul_nsmul])).eq

theorem exists_aut : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ ψ : (TFK (R := R) F ⊗ A.A) ≅ (TFK (R := R) F ⊗ A.A), ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q ψ.hom := by
  intro hL R _ _ _ I hI D A G _ _ hS U F _ _ _ k hk p
  have hG := hL.1.globalFns
  have hN : ∀ n, 1 ≤ k * (n + 1) := fun n => Nat.mul_pos hk n.succ_pos
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨w, hw⟩ := exists_frame D.toPre F k p.g.b
  choose ω hω vω using fun n => exists_frame_pow w hw (n + 1)
  let q : ∀ n, QkPt D.toPre F (k * (n + 1)) := fun n =>
    ⟨(n + 1) • p.y, p.g, exists_qk_mul D.tau_bimult p (n + 1)⟩
  choose Φ hΦ using fun n => GlobalTheory.T.thetaOperators_projective_representation hL R I hI D F (k * (n + 1)) (hN n)
  have hΦ' := fun n => (hΦ n).1 (q n) (ω n) (hω n)
  choose Ψ lin ex un using fun n => exists_transport hG U F (hN n) hw₀ _ (hΦ' n).1
  have mul : ∀ m : Fin 3 → ℕ, m 2 = m 0 + m 1 + 1 → ∀ t : ∀ i, SecA A F (k * (m i + 1)),
      (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) →
      ∀ z J, Good A.L z J → sA (Ψ _ (t 2)) (𝟙 _) z J = sA (Ψ _ (t 0)) (𝟙 _) z J * sA (Ψ _ (t 1)) (𝟙 _) z J := by
    intro m hm t
    choose s hs hs' using fun i => ex (m i) (t i)
    exact GlobalTheory.T.heckeOperator_multiplicative_on_section_products hL R I hI D A G hS U F w₀ hw₀ k hk p w hw (fun i => m i + 1) (fun i => k * (m i + 1))
      (fun i => ⟨Nat.succ_pos _, rfl⟩) (by show m 2 + 1 = m 0 + 1 + (m 1 + 1); omega) (fun i => q (m i))
      (fun i => ω (m i)) (fun i => ⟨rfl, rfl, hω _, vω _⟩) t (fun i => Ψ _ (t i)) s _
      (fun i => ⟨hs i, hs' i, ((hΦ' _).2 _ _).2 rfl⟩)
  obtain ⟨ψ, hψ, hα⟩ := GlobalTheory.T.exists_automorphism_of_multiplicative_section_family F _ A (jFK (R := R) F) k hk Ψ lin (fun a b s s' s'' h =>
    (mul_chart_iff A.isLB _ _ _ _).2 (mul ![a, b, a + b + 1] rfl
      (Fin.cons s (Fin.cons s' (Fin.cons s'' finZeroElim))) ((mul_chart_iff A.isLB _ _ _ _).1 h)))
  refine ⟨ψ, fun n N hn hN' q' hy hg => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hN'
  obtain rfl : q' = q n := GlobalTheory.TorusExt.qk_ext hy hg
  obtain ⟨α, hα, tw⟩ := hα n
  refine ⟨hψ, fun w₁ hw₁ => ⟨α, ω n, hα, hω n, fun t t' s s' h h' H => ?_⟩⟩
  obtain rfl : t' = Ψ n t := sec_ext' A.isLB fun y J hJ =>
    (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A H (𝟙 _) y hJ).trans
      (GlobalTheory.ThetaLin.sval_of_isTwistPull A.A (tw t) (𝟙 _) y hJ).symm
  exact ((hΦ' n).2 _ _).2 (un n w₁ hw₁ t s s' h h')

end GlobalTheory.InducingAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMorphismToProjectiveOfRankOneSectionsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_to_projective_of_rank_one_sections : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X : Scheme.{0}) (f' : X ⟶ Spec (CommRingCat.of R)) (N : LB X) (m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → (∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k, MvPolynomial.eval₂Hom (cst f (H.U k)) (fun i => (s i).f k) F = 0) → ∀ j k, MvPolynomial.eval₂Hom (cst f' (N.U k)) (fun i => (w i j).f k) F = 0) → ∃ φ : X ⟶ Z, φ ≫ f = f' ∧ ∀ (T : Scheme.{0}) (r : T ⟶ X) (ψ : T ⟶ Z), ψ ≫ f = r ≫ f' → (∀ z k k' i i' j, ψ z ∈ H.U k → r z ∈ N.U k' → gs ψ z (H.U k) ((s i).f k) * gs r z (N.U k') ((w i' j).f k') = gs ψ z (H.U k) ((s i').f k) * gs r z (N.U k') ((w i j).f k')) → r ≫ φ = ψ := by
  first | exact @GlobalTheory.RankMap.exists_hom_of_rank_one | exact GlobalTheory.RankMap.exists_hom_of_rank_one | (intros; apply GlobalTheory.RankMap.exists_hom_of_rank_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Algebraise
variable {X Y : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (rs_rs h₁ h₂ u.val)

theorem pw_pw (H : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw H a) b = AbLaw.pw H (a * b) := by
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem pw_pull (H : LB X) (f : Y ⟶ X) (a : ℤ) :
    (AbLaw.pw H a).pull f = AbLaw.pw (H.pull f) a := by
  have : ((AbLaw.pw H a).pull f).g = (AbLaw.pw (H.pull f) a).g := by
    funext j j'
    change (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k) ^ a))) ^ (1 : ℤ)) =
      (∏ k : PUnit, (res _ (pullU f _ (H.g (j k) (j' k)))) ^ (1 : ℤ)) ^ a
    simp only [Fintype.prod_unique, zpow_one, map_zpow]
  exact congrArg (fun g => (⟨(H.pull f).ι, (H.pull f).U, g⟩ : LB Y)) this

theorem lbIso_pw {A B : LB X} (h : LBIso A B) (a : ℤ) : LBIso (AbLaw.pw A a) (AbLaw.pw B a) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => (w.s p) ^ a⟩, fun p q => ?_⟩
  have key : ∀ {G : Type} [CommGroup G] {x y z u : G}, x = y * z⁻¹ * u →
      x ^ a = y ^ a * (z ^ a)⁻¹ * u ^ a := by
    rintro G _ x y z u rfl
    rw [mul_zpow, mul_zpow, inv_zpow]
  change res _ (w.s p ^ a) = (res _ (B.g p.1 q.1 ^ a) * (res _ (A.g p.2 q.2 ^ a))⁻¹) * res _ (w.s q ^ a)
  rw [map_zpow, map_zpow, map_zpow, map_zpow]
  exact key (hw p q)

theorem cocycle_on {H : LB X} (hH : H.IsLB) (i j k : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hj : W ≤ H.U j) (hk : W ≤ H.U k) :
    res (le_inf hi hj) (H.g i j) * res (le_inf hj hk) (H.g j k) = res (le_inf hi hk) (H.g i k) := by
  have h := congrArg (res (le_inf (le_inf hi hj) hk : W ≤ H.U i ⊓ H.U j ⊓ H.U k)) (hH.cocycle i j k)
  simpa only [map_mul, res_res] using h

theorem rel_on {H : LB X} (hH : H.IsLB) (i k i' k' : H.ι) {W : X.Opens} (hi : W ≤ H.U i)
    (hk : W ≤ H.U k) (hi' : W ≤ H.U i') (hk' : W ≤ H.U k') :
    res (le_inf hi hk) (H.g i k) = res (le_inf hi hi') (H.g i i') * (res (le_inf hk hk') (H.g k k'))⁻¹ *
      res (le_inf hi' hk') (H.g i' k') := by
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq, cocycle_on hH i k k' hi hk hk',
    cocycle_on hH i i' k' hi hi' hk']

theorem lbIso_tw {H : LB X} (hH : H.IsLB) (t : ℤ) : LBIso (AbLaw.pw H (t + 1)) (tw H H t) := by
  refine ⟨⟨fun p => res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      H.U p.1.1 ⊓ H.U p.1.2 ⊓ H.U p.2 ≤ H.U p.1.1 ⊓ H.U p.2) (H.g p.1.1 p.2) *
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      H.U p.1.1 ⊓ H.U p.1.2 ⊓ H.U p.2 ≤ H.U p.1.2 ⊓ H.U p.2) (H.g p.1.2 p.2) ^ t⟩, ?_⟩
  rintro ⟨⟨i, j : H.ι⟩, k : H.ι⟩ ⟨⟨i', j' : H.ι⟩, k' : H.ι⟩
  let W : X.Opens := H.U i ⊓ H.U j ⊓ H.U k ⊓ (H.U i' ⊓ H.U j' ⊓ H.U k')
  have hi : W ≤ H.U i := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hj : W ≤ H.U j := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hk : W ≤ H.U k := inf_le_left.trans inf_le_right
  have hi' : W ≤ H.U i' := inf_le_right.trans (inf_le_left.trans inf_le_left)
  have hj' : W ≤ H.U j' := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have hk' : W ≤ H.U k' := inf_le_right.trans inf_le_right
  change res (inf_le_left : W ≤ H.U i ⊓ H.U j ⊓ H.U k) (res _ (H.g i k) * res _ (H.g j k) ^ t) =
    (res (V := W) (U := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _
        (res (V := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _ (H.g i i') *
          (res (V := H.U i ⊓ H.U j ⊓ (H.U i' ⊓ H.U j')) _ (H.g j j' ^ (-t)))⁻¹) *
      (res (V := W) _ (H.g k k' ^ (t + 1)))⁻¹) *
    res (inf_le_right : W ≤ H.U i' ⊓ H.U j' ⊓ H.U k') (res _ (H.g i' k') * res _ (H.g j' k') ^ t)
  simp only [map_mul, map_inv, map_zpow, res_res]
  erw [res_res, res_res]
  rw [rel_on hH i k i' k' hi hk hi' hk', rel_on hH j k j' k' hj hk hj' hk']
  simp only [zpow_neg, inv_inv, mul_zpow, inv_zpow, zpow_add_one, mul_inv]
  ac_rfl

theorem exists_veryAmple_h1Zero (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) (L : LB B.left) (hL : L.IsLB) (h : RelAmple B L) :
    ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes (AbLaw.pw L d) ∧
      ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (AbLaw.pw L d)), VeryAmpleBy B.hom (AbLaw.pw L d) s := by
  obtain ⟨d₀, hd₀, n₀, s₀, hs₀⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  have hH := isLB_pw hL (d₀ : ℤ)
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 R B.left B.hom _ n₀ s₀ hH hs₀ _ hH
  have h1 := ht₀ (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  obtain ⟨w, hw⟩ := lbIso_tw hH (t₀.toNat : ℤ)
  have h2 := H1Iso.firstCohomologyVanishes_of_iso_of_isGen (isLB_tw hH hH _).cover (isLB_pw hH _) w hw h1
  have h3 := veryAmpleBy_pw R B.left B.hom _ n₀ s₀ hH hs₀ (t₀.toNat + 1) (Nat.le_add_left _ _)
  have e : AbLaw.pw (AbLaw.pw L (d₀ : ℤ)) ((t₀.toNat + 1 : ℕ) : ℤ) =
      AbLaw.pw L ((d₀ * (t₀.toNat + 1) : ℕ) : ℤ) := by
    rw [pw_pw, Nat.cast_mul]
  refine ⟨d₀ * (t₀.toNat + 1), Nat.mul_pos hd₀ (Nat.succ_pos _), ?_, ?_⟩
  · rw [← e, Nat.cast_add, Nat.cast_one]
    exact h2
  · rw [← e]
    exact h3

theorem algebraisation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → (∀ e, Flat (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of V))) (M H : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left) (n d : ℕ) (s : Fin (n + 1) → LB.Sec H), M.IsLB ∧ H.IsLB ∧ Flat B.hom ∧ VeryAmpleBy B.hom H s ∧ 1 ≤ d ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) ∧ LBIso (pw (N e) d) (H.pull (b e)) := by
  intro V _ _ _ _ Y β hβ hY N v hN hA
  obtain ⟨d, hd, h0, n, s₀, hs₀⟩ := exists_veryAmple_h1Zero _ (Y 0) (N 0) (hN 0).1 hA
  have hv : ∀ e, LBIso (AbLaw.pw (N e) d) ((AbLaw.pw (N (e + 1)) d).pull (β e)) := fun e => by
    rw [pw_pull]
    exact lbIso_pw ⟨v e, (hN e).2⟩ d
  choose v' hv' using hv
  have hN' : ∀ e, (AbLaw.pw (N e) d).IsLB ∧ (v' e).IsGen := fun e => ⟨isLB_pw (hN e).1 d, hv' e⟩
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections V Y β hβ hY
    (fun e => AbLaw.pw (N e) d) v' hN' h0 (s₀ j)
  have hva : VeryAmpleBy (Y 0).hom (AbLaw.pw (N 0) d) (fun j => s j 0) := by
    have : (fun j => s j 0) = s₀ := funext hs0
    rw [this]
    exact hs₀
  obtain ⟨B, H, s', b, w, hH, hB, hb, hbβ, hw, -⟩ := GlobalTheory.Unif.exists_projective_of_formal_embedding V Y β hβ hY
    (fun e => AbLaw.pw (N e) d) v' hN' n (fun e j => s j e) (fun e j => hs j e) hva
  have hP : IsProjBy B.hom := ⟨H, hH, n, s', hB⟩
  have := isProper_of_isProjBy V B.left B.hom hP
  have hF : Flat B.hom := GlobalTheory.FlatThickenings.flat_of_flat_thickenings V B Y b hb hY
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.LBAlg.exists_lineBundle_of_thickenings V Y β hβ B b hP hF hb hbβ N v hN
  exact ⟨B, M, H, b, n, d, s', hM, hH, hF, hB, hd, hb, hbβ, fun e => ⟨hNM e, w e, (hw e).1⟩⟩

end GlobalTheory.Algebraise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElementStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_sq_eq_of_symmetric_thetaElement : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (w₀ : W0 U.toUnifPre) (w : Frm D.toPre F N p.g.b), w₀.IsGen → w.IsGen → (∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s') → (∃ nu : LB.Gen (negLB A.A A.L N (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L N θ nu) (LB.oneGen A.L)) → ∀ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4) ![(𝟙 D.toPre.P.A ^ (N + 1)).left, (𝟙 D.toPre.P.A ^ N).left, 𝟙 _, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]), Normd ν → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J := by
  first | exact @GlobalTheory.SymFrame.sq_frame_of_symmetric | exact GlobalTheory.SymFrame.sq_frame_of_symmetric | (intros; apply GlobalTheory.SymFrame.sq_frame_of_symmetric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtDvrAndLaws
section
open ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory

theorem homExtDvr_and_laws : Out.HomExtDvrSt ∧ Out.Laws7 := by
  have h : Out.HomExtDvrSt := fun T _ _ _ G G' _ _ hG hG' φ hφ =>
    GlobalTheory.existsUnique_hom_extension_semiAbelian T (FractionRing T) G G' hG hG' φ hφ
  exact ⟨h, ⟨h⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivTorusQuotientTowerAlgebraisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.Principal

theorem finite_points {S : Scheme.{0}} (H : Over S) [IsFinite H.hom] {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) : Finite (Over.mk t ⟶ H) := by
  have hfin := ((pullback.snd H.hom t).finite_preimage_singleton (IsLocalRing.closedPoint K)).to_subtype
  let σ : (Over.mk t ⟶ H) → (Spec (CommRingCat.of K) ⟶ pullback H.hom t) := fun x =>
    pullback.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp _).symm)
  have h₁ : ∀ x, σ x ≫ pullback.fst H.hom t = x.left := fun x => pullback.lift_fst _ _ _
  have h₂ : ∀ x, σ x ≫ pullback.snd H.hom t = 𝟙 _ := fun x => pullback.lift_snd _ _ _
  refine Finite.of_injective (fun x => (⟨σ x (IsLocalRing.closedPoint K),
    Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _⟩ :
      (pullback.snd H.hom t) ⁻¹' {IsLocalRing.closedPoint K})) fun a b hab => ?_
  have e : σ a = σ b :=
    ext_of_apply_closedPoint_eq (K := K) (pullback.snd H.hom t) (h₂ a) (h₂ b) (congrArg Subtype.val hab)
  exact Over.OverMorphism.ext ((h₁ a).symm.trans (e ▸ h₁ b))

theorem exists_pow_eq_one (hG : GlobalFnsSt) {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {L : LB B.left} (hLB : L.IsLB) (hL : RelAmple B L)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ B) (hx : InK B L x) : ∃ N : ℕ, 1 ≤ N ∧ x ^ N = 1 := by
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG R B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ x : Over.mk t ⟶ B, InK B L x ↔ ∃ y : Over.mk t ⟶ H, y ≫ j = x :=
    fun x => (hK _ rfl _ x).trans (hH _ x)
  have := finite_points H t
  have : Finite (kSubgroup B hLB (Over.mk t)) :=
    Finite.of_surjective (fun y : Over.mk t ⟶ H => (⟨y ≫ j, (hrep _).2 ⟨y, rfl⟩⟩ : kSubgroup B hLB (Over.mk t)))
      fun z => ((hrep z.1).1 z.2).imp fun _ h => Subtype.ext h
  exact ⟨Nat.card (kSubgroup B hLB (Over.mk t)), Nat.card_pos,
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : kSubgroup B hLB (Over.mk t))))⟩

theorem exists_gen_of_inK {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hLB : L.IsLB)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk t ⟶ B) (hx : InK B L x) :
    ∃ u : LB.Gen (translDiff B L x), u.IsGen := by
  obtain ⟨V, hpV, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  refine GlobalTheory.TwistTranslate.gen_of_pull_top hLB _ (fun z => ?_) c hc
  have e : ∀ p q : Spec (CommRingCat.of K), p = q := fun p q => Subsingleton.elim p q
  change (fst (Over.mk t) B).left z ∈ V
  rw [e ((fst (Over.mk t) B).left z) (IsLocalRing.closedPoint K)]
  exact hpV

theorem kTriv_alg : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L := by
  intro hc laws V _ _ _ A G _ _ s t a
  have hdvr : IsDiscreteValuationRing V := s.cdvr.1
  have hchar : CharZero V := s.cdvr.2.2
  refine GlobalTheory.KTrivGeneric.kTriv_of_generic laws.globalFns V a.B a.isAb a.M.L a.M.c a.ample fun x hx => ?_
  obtain ⟨N, hN, hxN⟩ := exists_pow_eq_one laws.globalFns a.isAb a.M.L.isLB a.ample _ x hx
  exact GlobalTheory.UU.cubWeil_nondegenerate_generic hc laws V A G s t a (AlgebraicClosure (FractionRing V)) N hN x hxN fun y hy =>
    GlobalTheory.UU.KerPair.cubWeil_of_gen laws.globalFns _ a.B a.isAb a.M.L a.M.c N _ x y hxN hy
      (exists_gen_of_inK a.M.L.isLB _ x hx)

end GlobalTheory.UU.Principal
end

