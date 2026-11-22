import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCpOfGenericPolarisation
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.SymExtend

theorem exists_normalised {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = 1)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (b : Z ⟶ S) (z : Z) (J), Good L z J → val u (b ≫ e) z J = 1 := by
  obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := ε)
    (fun V _ k => by
      have q := h0 V (fun χ => k (p ≫ χ))
      refine Eq.trans (DVR.prod_sum₂ (K := K) (K' := K) (U := V) _
        (c := ∏ i, k (φ i) ^ ε i) rfl
        (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by
          show k ((p ≫ e) ≫ _) ^ _ = _
          rw [Category.assoc]).trans q))) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (p ≫ e))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨t', ht', fun Z b z J hJ => ?_⟩
  have : (b ≫ e) ≫ p ≫ e = b ≫ e := by
    rw [Category.assoc, ← Category.assoc e, he, Category.id_comp]
  rw [hv Z _ z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]

theorem prod_sym_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (U : Type) [CommGroup U]
    (h : (S ⟶ G.left) → U) :
    ∏ k : Fin 2, h (eSec G ≫ ![(ι[G]).left, 𝟙 G.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 :=
  (prod_sym (η[G]) h).trans (by
    have e : (η[G])⁻¹ = η[G] := (GrpObj.one_inv : η[G] ≫ ι[G] = η[G])
    rw [e, mul_inv_cancel])

theorem sym_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) (k : Fin 2) :
    ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := by
  fin_cases k
  · have := inv_left_comp mul (𝟙 G')
    rw [Hom.inv_def, Category.id_comp] at this
    exact this.trans (congrArg (· ≫ _) (Category.id_comp F))
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem surjective_cube_of_generic (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [Flat G.hom]
    {A : Over (Spec (CommRingCat.of (FractionRing R)))} [GrpObj A] (hA : IsAbelianScheme A)
    (gen : (Over.pullback (jK R)).obj G ≅ A) : Function.Surjective (G3 G).hom.appTop.hom := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (gen.inv.left ≫ pullback.fst G.hom (jK R)) A.hom G.hom (jK R) := by
    have : IsIso gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map gen.inv))
    have s : IsPullback gen.inv.left A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    RigidIsoCube.surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ hA).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G hA hg _)
      (surj_comp (RigidIsoCube.surjective_snd_of_generic hG (jK R) G hA hg _) s₁)
  rwa [Over.w, Over.w] at sj

theorem exists_sym (hG : GlobalFnsSt) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (gen : (Over.pullback (jK V)).obj G ≅ A.A)
    [IsMonHom gen.hom] (L : LB G.left) (hL : L.IsLB)
    (w : LB.Iso (A.L.pull gen.hom.left) (L.pull (pullback.fst G.hom (jK V)))) (hw : w.IsGen) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L) := by
  have := A.isAb.comm
  let G' : Over (Spec (CommRingCat.of (FractionRing V))) := (Over.pullback (jK V)).obj G
  let j : pullback G.hom (jK V) ⟶ G.left := pullback.fst G.hom (jK V)
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG A.isAb A.isLB A.sym
  obtain ⟨a, ha, -⟩ := CubTransport.exists_pmaps ((isGen_iff _).1 (pullIso_isGen A.isLB gen.hom.left)) A.isLB
    (pull_isLB A.isLB _) gen.hom.left
    (sym_comp (f := 𝟙 _) (hw := by simp) (toBase_mul_of_isMonHom gen.hom _)) u hu
  obtain ⟨t₀, ht₀, -⟩ := exists_up ((isGen_iff _).1 hw) hL (pull_isLB A.isLB _) a ha
  obtain ⟨t₁, ht₁, -⟩ := exists_gen hL (φ' := fun k => j ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) (ε' := ![1, -1])
    (fun U _ h => Finset.prod_congr rfl fun k _ =>
      congrArg (fun q => h q ^ _) (sym_comp (toBase_mul_pullback G (jK V)) k)) t₀ ht₀
  have e₂ : eSec G' ≫ j = jK V ≫ eSec G := (cubeMapOf (isGrpPullback_pullback G (jK V))).e_comm
  obtain ⟨t, ht, hv⟩ := exists_normalised hL G'.hom (eSec G') (Over.w η[G']) (fun U _ h => by
    refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (prod_sym_unit G U fun q => h (jK V ≫ q))
    exact congrArg (fun q => h q ^ _) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans
      (Category.assoc _ _ _)))) t₁ ht₁
  obtain ⟨ρ, hρ, hρv⟩ := exists_gen hL (φ' := fun k => eSec G ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k)
    (ε' := ![1, -1]) (fun U _ h => (Fintype.prod_empty _).trans (prod_sym_unit G U h).symm)
    (LB.oneGen L) (LB.isGen_oneGen L)
  obtain ⟨s₀, ⟨hs₀, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V (FractionRing V) G.left G.left G.hom (eSec G)
    inferInstance (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance)
    (Over.w η[G]) (eSec G') e₂ L hL (Fin 2) _ _ t ρ ht hρ (corr_of_val hL fun y J hJ =>
      ((val_pull hJ t _ _).trans (hv _ _ y J hJ)).trans
        ((val_pull hJ ρ _ _).trans ((hρv _ _ y J hJ).trans (val_one _))).symm)
  obtain ⟨s, hs, hsv⟩ := exists_normalised hL G.hom (eSec G) (Over.w η[G]) (prod_sym_unit G) s₀ hs₀
  exact ⟨s, hs, corr_of_val hL fun y J hJ =>
    ((val_pull hJ s _ _).trans (hsv _ _ y J hJ)).trans (val_one _).symm⟩

end GlobalTheory.SymExtend

namespace GlobalTheory

theorem exists_cp_of_generic_polarisation : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (LG : RigLB G) (c : CubicalStr G LG) (w : LB.Iso (A.L.pull gen.hom.left) (LG.L.pull (pullback.fst G.hom (jK V)))), w.IsGen → ∃ P : CP G, P.L = LG ∧ HEq P.c c := by
  intro hL V _ _ _ hV A G _ _ hG gen hgen LG c w hw
  have := hV.1
  have := hG.smooth
  have := hG.geomConnected
  obtain ⟨s, hs, hr⟩ := SymExtend.exists_sym hL.globalFns V A G gen LG.L LG.isLB w hw
  exact ⟨CP.ofSurjective (SymExtend.surjective_cube_of_generic hL.globalFns G A.isAb gen) LG c s hs hr, rfl, HEq.rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefUnit
open GlobalTheory.UT.CoefBasic

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem point_ext {X : Scheme.{0}} [X.IsSeparated] (x₁ x₂ : (TWM.TO hϖ hv).left ⟶ X)
    (h : (TWM.ιS hϖ hv).left ≫ x₁ = (TWM.ιS hϖ hv).left ≫ x₂) : x₁ = x₂ := by
  have hU : ValuativeCriterion.Uniqueness (terminal.from X) := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq (terminal.from X) :=
    { R := TWO.Ov v, K := F, i₁ := (TWM.ιS hϖ hv).left ≫ x₁, i₂ := terminal.from _,
      commSq := ⟨terminal.hom_ext _ _⟩ }
  have := (hU S).elim ⟨x₁, rfl, terminal.hom_ext _ _⟩ ⟨x₂, h.symm, terminal.hom_ext _ _⟩
  exact congrArg CommSq.LiftStruct.l this

theorem exists_ratio_nonneg {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, 0 ≤ v x ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨s, hs⟩ := exists_sec hL h (Geo.Tor.genSec t ht)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.TwistUnit.exists_ratio_local (R := TWO.Ov v) hL s t' ht'
  refine ⟨TWM.ιr (v := v) x₀, TWM.v_ιr x₀, fun z J hJ => ?_⟩
  have e := gs_pull (𝟙 _) (TWM.ιS hϖ hv).left z ⊤ trivial x₀
  rw [Category.id_comp] at e
  have e' := e.symm.trans (congrArg (gs (𝟙 _) z ⊤)
    (TWM.appTop_specMap (CommRingCat.ofHom (algebraMap (TWO.Ov v) F)) x₀))
  exact (sval_genSec t ht _ z hJ).symm.trans ((hs _ _ z J hJ).symm.trans
    ((hx₀ _ _ z J hJ).trans (congrArg (· * _) e')))

theorem exists_ratio_zero {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, v x = 0 ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨x, hx, e⟩ := exists_ratio_nonneg hϖ hv hL h t ht t' ht'
  obtain ⟨y, hy, e'⟩ := exists_ratio_nonneg hϖ hv hL (fun U _ g => (h U g).symm) t' ht' t ht
  refine ⟨x, le_antisymm (TWO.le_zero_of_add_eq_zero_nonneg ?_ hy) hx, e⟩
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have a := e z J hJ
  rw [e' z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, ← map_mul] at a
  have b : cstH z (x * y) = 1 := by
    rw [← Units.mul_left_inj (val t (TWM.ιS hϖ hv).left z J), _root_.one_mul]; exact a.symm
  rw [← AddValuation.map_mul, cstH_inj z (b.trans (map_one _).symm), AddValuation.map_one]

theorem v_of_isCoef {D : DegData V (maximalIdeal V)} {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b}
    {χ : D.toPre.X} {l ω : ℚ} (hg : GenV hϖ hv (g.s χ) l) (hw : GenV hϖ hv w ω)
    (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (hm : TWM.ιS hϖ hv ≫ m = g.b)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)))
    (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => m.left ≫ DegPre.famφB D.toPre χ i) (DegPre.famε k)))
    (hG₀ : G₀.IsGen) (x : F)
    (hs : ∀ z J, Good D.toPre.P.L z J → sval s (lift (𝟙 (TF (R := V) F)) g.b).left z J =
      cst (R := V) F z x * (val G₀ (TWM.ιS hϖ hv).left z J).val) :
    ∃ c, IsCoef k g w χ s c ∧ v c = v x + ((l + ω : ℚ) : WithTop ℚ) := by
  have hL := D.toPre.P.isLB
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨φ₁, h₁, t₁, ht₁, x₁, v₁, e₁⟩ := hg
  obtain ⟨φ₂, h₂, t₂, ht₂, x₂, v₂, e₂⟩ := hw
  have c₁ : TWM.ιS hϖ hv ≫ cP D.toPre _ χ = cP D.toPre _ χ := comp_cP D.toPre _ χ
  have c₂ : TWM.ιS hϖ hv ≫ (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A) = 1 := MonObj.comp_one _
  have c₃ : TWM.ιS hϖ hv ≫ (cP D.toPre _ χ * m) = cP D.toPre _ χ * g.b := by
    rw [MonObj.comp_mul, c₁, hm]
  obtain rfl : φ₁ = TWM.gtφO hϖ hv m χ := funext fun i => point_ext hϖ hv _ _ ((h₁ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₃.symm, congrArg (·.left) c₁.symm, congrArg (·.left) hm.symm,
      congrArg (·.left) c₂.symm]))
  obtain rfl : φ₂ = TWM.lineφO hϖ hv m := funext fun i => point_ext hϖ hv _ _ ((h₂ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₂.symm, congrArg (·.left) hm.symm]))
  obtain ⟨u, hu, eu⟩ := exists_ratio_zero hϖ hv hL (fun U _ h => by
      have p := SectionScalarValuation.prod_famB D.toPre m χ k h
      have q : (TWM.TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left := rfl
      have r : m * SectionScalarValuation.cQ D.toPre _ χ = cP D.toPre _ χ * m := mul_comm _ _
      have r' : SectionScalarValuation.cQ D.toPre (TWM.TO hϖ hv) χ = cP D.toPre _ χ := rfl
      rw [r, r'] at p
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p, Fintype.prod_unique (_ : PUnit → U), q]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, TWM.gtφO, TWM.lineφO, DegPre.gtε, DegPre.lineε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ G₀ t₁) t₂)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hG₀ ht₁) ht₂)
    (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TWM.TO hϖ hv).hom)
    (DVR.pullGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ D.toPre.rig_gen k) _)
  refine ⟨x * x₁ * x₂ * u, fun z J hJ => ?_, ?_⟩
  · have a := eu z J hJ
    rw [val_mul hJ, val_mul hJ, val_pull hJ, Over.w (TWM.ιS hϖ hv)] at a
    have b : val (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TF (R := V) F).hom z J = rigV D.toPre (TF (R := V) F).hom z J ^ k := map_pow _ _ _
    rw [b, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val] at a
    rw [hs z J hJ, e₁ z J hJ, e₂ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination (-(cstH z x * cstH z x₁ * cstH z x₂)) * a
  · rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hu, v₁, v₂, add_zero, add_assoc,
      WithTop.coe_add]

end

theorem exists_fam_coef_val : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 4 ≤ k → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) l ω, w.IsGen → GtV hϖ hv g l → GenV hϖ hv w ω → ∀ a₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, (s.s β).f j = 0) ∧ v (coef s g w a₀) = (((Q a₀ : ℚ) / k + l a₀ + ω : ℚ) : WithTop ℚ) := by
  intro hLL hT _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk g w l ω hw hg hω a₀
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hs⟩ :=
    GlobalTheory.exists_integral_section_unit_at hLL.1 hT V ϖ hϖ D Q hQ F v hv k hk a₀ m
  rw [hm] at hs
  obtain ⟨c, hc, vc⟩ := v_of_isCoef hϖ hv (hg a₀) hω m hm σ G₀ hG₀ x hs
  obtain ⟨s₀, rfl, h₀⟩ := GlobalTheory.FamFree.exists_fam_single hLL.1.globalFns D.tau_bimult (by omega : 1 ≤ k) a₀ σ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F, v ζ = (((Q a₀ : ℚ) / k : ℚ) : WithTop ℚ) := by
    by_cases h : a₀ = 0
    · exact ⟨1, by rw [h, QForm.Q_zero hϖ D hQ, AddValuation.map_one]; simp⟩
    · have h1 := QForm.Q_pos hϖ D hQ h
      obtain ⟨ζ, -, e⟩ := exists_val_eq hv (r := (Q a₀ : ℚ) / k)
        (div_pos (by exact_mod_cast (by omega : (0 : ℤ) < Q a₀)) (by exact_mod_cast (by omega : 0 < k)))
      exact ⟨ζ, e⟩
  have hsm : Fam.IsSmul D.toPre F ζ s₀ (ζ • s₀) := (isSmul_iff _ _ _).2 rfl
  have hz : ∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, ((ζ • s₀).s β).f j = 0 := fun β hβ j => by
    rw [hsm β j, h₀ β (fun mu e => hβ mu e.symm) j]; exact mul_zero _
  refine ⟨ζ • s₀, fun χ => ?_, hz, ?_⟩
  · by_cases h : ∃ z : D.toPre.X, χ = a₀ + k • z
    · obtain ⟨z, rfl⟩ := h
      have H := SectionScalarValuation.fe_move hϖ hQ hv k z a₀ (ζ • s₀) (hσ.smul hζ.ge (hsm a₀))
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have e : 0 + (Q a₀ : ℚ) / k + ((k * Q z + QForm.bOf D.toPre Q z a₀ : ℤ) : ℚ) =
          0 + (Q (a₀ + k • z) : ℚ) / k := by
        rw [q_shift hϖ hQ a₀ z k]; push_cast; field_simp; ring
      rwa [e] at H
    · exact vge_of_zero (hz χ fun z e => h ⟨z, e⟩) _
  · have e : ζ • s₀ = (ζ - 1) • s₀ + s₀ := by rw [sub_smul, one_smul, sub_add_cancel]
    rw [e, ((coef_basic V D.toPre F k g).2.2 w hw).2.1, coef_eq hc, show (ζ - 1) * c + c = ζ * c by ring,
      AddValuation.map_mul, hζ, vc, hx, ← WithTop.coe_add, ← WithTop.coe_add, zero_add, add_assoc]

end GlobalTheory.UT.CoefUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenV
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO CoefBasic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
  {X : Scheme.{0}} {L : LB X}

theorem isDominant_ι : IsDominant (ιS hϖ hv).left := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap (algebraMap (Ov v) F))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (Ov v) F)]
  exact bot_le

theorem ι_inj [X.IsSeparated] : Function.Injective fun ψ : (TO hϖ hv).left ⟶ X => (ιS hϖ hv).left ≫ ψ := by
  intro a b h
  have := isDominant_ι hϖ hv
  have : IsReduced (TO hϖ hv).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (Ov v))))
  exact ext_of_isDominant (ιS hϖ hv).left h

theorem gs_ι (z : (TF (R := V) F).left) (a : Γ(Spec (CommRingCat.of (Ov v)), ⊤)) :
    gs (ιS hϖ hv).left z ⊤ a = cst F z (ιr (v := v) a) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := V) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap (Ov v) F)) a)

theorem sec_int [X.IsSeparated] (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = 1) :
    ∃ a : F, 0 ≤ v a ∧ ∀ z J, Good L z J → sval s (ιS hϖ hv).left z J = cst F z a := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιS hϖ hv).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj hϖ hv).extend_apply]) s
  have le : (⊤ : (TO hϖ hv).left.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → ((TO hϖ hv).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨ιr (v := v) (((TO hϖ hv).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), v_ιr _,
    fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι hϖ hv]
  exact (gs_res _ z le trivial _).symm

abbrev FS (V F : Type) [CommRing V] [IsDomain V] [Field F] [Algebra (FractionRing V) F] (X : Scheme.{0}) : Type 1 :=
  ∀ (U : Type) [CommGroup U], (((TF (R := V) F).left ⟶ X) → U) → U

def HV (L : LB X) (σ : FS V F X)
    (f : ∀ z : (TF (R := V) F).left, (((TF (R := V) F).left ⟶ X) → L.ι) → (TF (R := V) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TO hϖ hv).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ X) → U), ∏ i, h ((ιS hϖ hv).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιS hϖ hv).left z J).val

variable {hϖ hv}

theorem HV.mul {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x) (H' : HV hϖ hv L σ' f' x') :
    HV hϖ hv L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HV.one : HV hϖ hv L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TO hϖ hv).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HV.congr {σ σ' : FS V F X} {f f'} {x : F} (H : HV hϖ hv L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HV hϖ hv L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HV.pow {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (n : ℕ) :
    HV hϖ hv L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HV.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HV.smul {σ : FS V F X} {f} {x : F} (H : HV hϖ hv L σ f x) (c : F) :
    HV hϖ hv L σ (fun z J => cst F z c * f z J) (c * x) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  refine ⟨K, _, φ, ε, t, ht, hs, fun z J hJ => ?_⟩
  simp only [e z J hJ, cst_eq, map_mul, _root_.mul_assoc]

theorem HV.le [X.IsSeparated] (hL : L.IsLB) {σ : FS V F X} {f} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ f x') : v x ≤ v x' := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', mul_inv_cancel])
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : x' = x * a := by
    apply cstH_inj (R := V) z
    have d := (e z J hJ).symm.trans (e' z J hJ)
    rw [map_mul, ← cst_eq, ← cst_eq, ← cst_eq, ← b, Units.val_mul, ← _root_.mul_assoc, d, _root_.mul_assoc,
      Units.mul_inv, _root_.mul_one]
  rw [c, AddValuation.map_mul]
  exact le_add_of_nonneg_right ha

theorem HV.cmp [X.IsSeparated] (hL : L.IsLB) {σ σ' : FS V F X} {f f'} {x x' : F} (H : HV hϖ hv L σ f x)
    (H' : HV hϖ hv L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h)
    (hf : ∀ z J, Good L z J → f' z J = f z J) : v x = v x' :=
  le_antisymm ((H.congr hσ hf).le hL H') (H'.le hL (H.congr hσ hf))

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem hv_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem hv_sec [X.IsSeparated] (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TO hϖ hv).left ⟶ Y) {r : (TF (R := V) F).left ⟶ Y} (hr : (ιS hϖ hv).left ≫ r₀ = r) :
    ∃ x, 0 ≤ v x ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) x := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := Ov v) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, ha, hav⟩ := sec_int hϖ hv hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, ha, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem hv_of_genV {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} {r : ℚ}
    (H : GenV hϖ hv t r) :
    ∃ x, v x = r ∧ HV hϖ hv L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  obtain ⟨φ₀, h₀, t₀, ht₀, x, hx, e⟩ := H
  exact ⟨x, hx, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], e⟩

theorem genV_unique [X.IsSeparated] (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)}
    {t : LB.Gen (LB.LinComb L φ ε)} {r r' : ℚ} (H : GenV hϖ hv t r) (H' : GenV hϖ hv t r') : r = r' := by
  obtain ⟨x, hx, a⟩ := hv_of_genV H
  obtain ⟨x', hx', a'⟩ := hv_of_genV H'
  have := a.cmp hL a' (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [hx, hx'] at this
  exact_mod_cast this

theorem exists_genV (hL : L.IsLB) {φ : K → ((TF (R := V) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιS hϖ hv).left ≫ ψ) : ∃ r, GenV hϖ hv t r := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := Ov v) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιS hϖ hv).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  obtain ⟨q, hq⟩ := wt_coe_of_ne (v := v) hc
  refine ⟨q, φ₀, h₀, t₀, ht₀, c, hq, fun z J hJ => ?_⟩
  have := e (TF (R := V) F).left (𝟙 (TF (R := V) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end GlobalTheory.UT.CoefVal
end
end

