import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FunEqZeroOfAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackOfCoprodJoin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.JoinPull

section Helpers

variable {X X₁ Z : Scheme.{0}} {N : LB X} {M : LB X₁} {e : X₁ ⟶ X} {π : N.ι → M.ι}

theorem part_g_of_eq (h : IsPart N M e π) (ψ : Z ⟶ X₁) (χ : Z ⟶ X) (hχ : χ = ψ ≫ e) (z : Z) (i j : N.ι)
    (hi : ψ z ∈ M.U (π i)) (hj : ψ z ∈ M.U (π j)) :
    gm χ z (N.U i ⊓ N.U j) (N.g i j) = gm ψ z (M.U (π i) ⊓ M.U (π j)) (M.g (π i) (π j)) := by
  subst hχ; exact h.g _ ψ z i j hi hj

theorem part_g_eq_one (h : IsPart N M e π) (hM : M.IsLB) (ψ : Z ⟶ X₁) (χ : Z ⟶ X) (hχ : χ = ψ ≫ e) (z : Z)
    (i j : N.ι) (e₀ : π i = π j) (hi : ψ z ∈ M.U (π i)) : gm χ z (N.U i ⊓ N.U j) (N.g i j) = 1 := by
  rw [part_g_of_eq h ψ χ hχ z i j hi (e₀ ▸ hi)]
  have : ∀ b, π i = b → gm ψ z (M.U (π i) ⊓ M.U b) (M.g (π i) b) = 1 := by
    rintro _ rfl; exact gm_self hM _ z hi
  exact this _ e₀

end Helpers

theorem exists_iso_of_joinGen : ∀ {X₁ X₂ : Scheme.{0}} (M : LB X₁) (M' : LB X₂), M.IsLB → M'.IsLB → Nonempty X₁ → Nonempty X₂ → ∀ (F : X₂ ⟶ X₁) (t : LB.Gen (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))))), t.IsGen → ∃ w : LB.Iso M' (M.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X₂) (z : Z) (J : (Z ⟶ X₂ ⨿ X₁) → (join M' M).ι), Good (join M' M) z J → gw w f z (rr J (f ≫ F)) (rl J f) = val t f z J := by
  intro X₁ X₂ M M' hM hM' h₁ h₂ F t ht
  obtain ⟨i₀⟩ := @nonempty_idx _ _ hM h₁
  obtain ⟨k₀⟩ := @nonempty_idx _ _ hM' h₂
  have hl := isPart_inl M' M
  have hr := isPart_inr M' M
  have le : ∀ a : (PUnit.{1} → M.ι) × M'.ι, (LB.div (M.pull F) M').U a ≤
      LB.wchart (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
        (Sum.elim (fun _ => (k₀, a.1 PUnit.unit)) (fun _ => (a.2, i₀))) := fun a y hy =>
    Set.mem_iInter.2 fun k => by
      rcases k with u | u
      · exact (hr.mem (k₀, a.1 PUnit.unit) (F y)).2 (mem_pull.1 hy.1)
      · exact (hl.mem (a.2, i₀) y).2 hy.2
  let c : ChartPull (LB.div (M.pull F) M')
      (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
        (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ)))) (𝟙 X₂) :=
    { idx := fun a => Sum.elim (fun _ => (k₀, a.1 PUnit.unit)) (fun _ => (a.2, i₀))
      le := le
      g := fun y a b ha hb => by
        refine (gm_div M' (M.pull F) (𝟙 X₂) y a b ⟨ha, hb⟩).trans ?_
        refine Eq.trans ?_ (gm_linComb (join M' M) _ _ (𝟙 X₂) y _ _ (le a ha) (le b hb)).symm
        rw [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique]
        exact congrArg₂ (· * ·)
          ((gm_pull_g M F (𝟙 X₂) y a.1 b.1 ha.1 hb.1).trans ((part_g_of_eq hr (𝟙 X₂ ≫ F) _
            (Category.assoc _ _ _).symm y (k₀, a.1 PUnit.unit) (k₀, b.1 PUnit.unit) (mem_pull.1 ha.1)
            (mem_pull.1 hb.1)).symm.trans (zpow_one _).symm))
          ((congrArg (·⁻¹) (part_g_of_eq hl (𝟙 X₂) _ rfl y (a.2, i₀) (b.2, i₀) ha.2 hb.2).symm).trans
            (zpow_neg_one _).symm) }
  refine ⟨cGen c t, cGen_isGen c ht, fun Z f z J hJ => ?_⟩
  have m : f z ∈ (LB.div (M.pull F) M').U (fun _ => rr J (f ≫ F), rl J f) :=
    ⟨mem_pull.2 (hr.good hJ (f ≫ F)), hl.good hJ f⟩
  have n := hJ.mem (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) f
  refine (gm_res f z _ m _).trans ((gen_trans ht f z (le _ m) n).trans ?_)
  have e₁ : trF (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl))
      (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))) f z
      (Sum.elim (fun _ => (k₀, rr J (f ≫ F))) (fun _ => (rl J f, i₀)))
      (fun k => J (f ≫ Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl) k)) = 1 := by
    rw [trF, Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_unique]
    exact (congrArg₂ (· * ·)
      ((congrArg (· ^ _) (part_g_eq_one hr hM (f ≫ F) _ (Category.assoc _ _ _).symm z
        (k₀, rr J (f ≫ F)) (J (f ≫ F ≫ coprod.inr))
        (congrArg (fun q => (J q).2) (Category.assoc _ _ _)) (hr.good hJ (f ≫ F)))).trans (one_zpow _))
      ((congrArg (· ^ _) (part_g_eq_one hl hM' f _ rfl z (rl J f, i₀) (J (f ≫ coprod.inl)) rfl
        (hl.good hJ f))).trans (one_zpow _))).trans (mul_one 1)
  exact (congrArg (· * _) e₁).trans (one_mul _)

end GlobalTheory.JoinPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionTransportPullbackIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso : ∀ {X X' : Scheme.{0}} (L : LB X) (L' : LB X') (f : X' ⟶ X) (w : LB.Iso L' (L.pull f)), L.IsLB → L'.IsLB → w.IsGen → ∀ (N : ℕ) (t : H0 L' N), ∃ s : SecK L f N, ∀ (Z : Scheme.{0}) (p : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' → sval s p z J = (gw w p z (J (p ≫ f)) (J' p) ^ N).val * sval t p z J' := by
  first | exact @GlobalTheory.Mum.exists_secK_of_iso_pull | exact GlobalTheory.Mum.exists_secK_of_iso_pull | (intros; apply GlobalTheory.Mum.exists_secK_of_iso_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.FieldBaseChange

def basisOfIsExtension {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) : Module.Basis I F W :=
  Module.Basis.mk (GlobalTheory.ConstFam.linearIndependent_of_isExtension ha B.linearIndependent) (by
    have h : Submodule.span K (Set.range B) ≤
        Submodule.comap a (Submodule.span F (Set.range fun i => a (B i))) :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [← ha.span, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range B) := B.span_eq ▸ Submodule.mem_top
    exact h hv)

theorem basisOfIsExtension_apply {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) (i : I) : basisOfIsExtension ha B i = a (B i) := by
  simp [basisOfIsExtension]

theorem exists_bijective_extension : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  intro K F V V' W W' _ _ _ _ _ _ _ _ _ _ _ a d ha hd e he
  let B := Module.Basis.ofVectorSpace K V
  let B' := B.map (LinearEquiv.ofBijective e he)
  let C := basisOfIsExtension ha B
  let C' := basisOfIsExtension hd B'
  let E := C.equiv C' (Equiv.refl _)
  refine ⟨E.toLinearMap, E.bijective, fun v => ?_⟩
  have key : (E.toLinearMap.comp a : V →ₛₗ[algebraMap K F] W') = d.comp e := B.ext fun i => by
    have h1 : a (B i) = C i := (basisOfIsExtension_apply ha B i).symm
    have h2 : d (e (B i)) = C' i := by
      rw [basisOfIsExtension_apply hd B' i]; simp [B']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, h2, E, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun key v

end GlobalTheory.FieldBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapThetaGroupActionSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem exists_linear_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), ∃ b : SecF A F N →ₗ[F] SecF A F N, ∀ t t' : SecF A F N, IsActOf A.A A.L N θ t t' ↔ t' = b t := by
  intro R _ _ A F _ _ N θ
  have hex : ∀ t : SecF A F N, ∃ u : SecF A F N, IsActOf A.A A.L N θ t u :=
    fun t => GlobalTheory.VVCompare.exists_isActOf A.A A.isLB θ t
  choose Θ hΘ using hex
  have hb : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : translT A.A θ.pt ≫ fst _ _ = _)
  have hv := fun (t u : SecF A F N) (h : IsActOf A.A A.L N θ t u) y J hJ =>
    GlobalTheory.VVCompare.sv_of_isTwistPull A.A h (𝟙 _) y (J := J) hJ
  refine ⟨⟨⟨Θ, fun s s' => sec_ext' A.isLB fun y J hJ => ?_⟩,
    fun c s => sec_ext' A.isLB fun y J hJ => ?_⟩, fun t t' => ⟨fun h => sec_ext' A.isLB fun y J hJ => ?_, ?_⟩⟩
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_add' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_add' hJ _ s s')).symm))
    exact (congrArg₂ (· + ·) (hv _ _ (hΘ s) y J hJ) (hv _ _ (hΘ s') y J hJ)).trans (mul_add _ _ _).symm
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_smul' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_smul' hJ _ c s)).symm))
    rw [Category.assoc, hb]
    exact (congrArg _ (hv _ _ (hΘ s) y J hJ)).trans (mul_left_comm _ _ _)
  · exact (hv _ _ h y J hJ).trans (hv _ _ (hΘ t) y J hJ).symm
  · rintro rfl
    exact hΘ t

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperato
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.PhiLinear

theorem exists_linear_phi : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : GlobalTheory.UT.Frm D.toPre F N p.g.b), GlobalTheory.UT.TXFrame N p w → ∃ a : Fam D.toPre F N →ₗ[F] Fam D.toPre F N, ∀ s s', PhiRel D.toPre F N p w s s' ↔ s' = a s := by
  intro R _ _ _ I _ D F _ _ _ N hN p w hw
  exact ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of_globalFns GlobalTheory.globalFns_holds R I D F N hN.pos p w hw.1

end GlobalTheory.Mum.PhiLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationProdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearization_prod : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ga Gb : Type) [Group Ga] [Group Gb] (ρ₁ : Ga → (X ⟶ X)) (ρ₂ : Gb → (X ⟶ X)) (ρ : Ga × Gb → (X ⟶ X)), (∀ p, ρ p = ρ₁ p.1 ≫ ρ₂ p.2) → (∀ a b, ρ₁ a ≫ ρ₂ b = ρ₂ b ≫ ρ₁ a) → (∀ a c, ρ₁ (a * c) = ρ₁ a ≫ ρ₁ c) → (∀ b d, ρ₂ (b * d) = ρ₂ b ≫ ρ₂ d) → ∀ (v₁ : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₁ a] ![1, -1])) (v₂ : ∀ b, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₂ b] ![1, -1])), (∀ a, (v₁ a).IsGen) → (∀ b, (v₂ b).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (v₁ (a * c)) (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₁ c) (ρ₁ a)))) → (∀ b d, LB.Gen.Corr L _ _ _ _ (v₂ (b * d)) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₂ d) (ρ₂ b)))) → (∀ a b, LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₂ b) (ρ₁ a))) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₁ a) (ρ₂ b)))) → ∃ u : ∀ p : Ga × Gb, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), (∀ p, (u p).IsGen) ∧ ∀ p q, LB.Gen.Corr L _ _ _ _ (u (p * q)) (LB.mulGen L _ _ _ _ (u p) (LB.pullGen L _ _ (u q) (ρ p))) := by
  first | exact @GlobalTheory.ProdLin.exists_linearisation_prod | exact GlobalTheory.ProdLin.exists_linearisation_prod | (intros; apply GlobalTheory.ProdLin.exists_linearisation_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionOfOpenImmersionSpec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.LocSecOfImm

theorem bij_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) [IsOpenImmersion q] (U : Y.Opens) (hU : U ≤ q.opensRange)
    (V : X.Opens) (h : V ≤ q ⁻¹ᵁ U) (h' : q ⁻¹ᵁ U ≤ V) : Function.Bijective (q.appLE U V h).hom := by
  obtain rfl : V = q ⁻¹ᵁ U := le_antisymm h h'
  have := q.isIso_app U hU
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (q.app U)

theorem appLE_res {X Y : Scheme.{0}} (q : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (h : U' ≤ U) (e : V ≤ q ⁻¹ᵁ U')
    (e' : V ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : (q.appLE U' V e).hom (resG Y h a) = (q.appLE U V e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.map_appLE e (homOfLE h).op)

theorem res_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (h : V' ≤ V) (e : V ≤ q ⁻¹ᵁ U)
    (e' : V' ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : resG X h ((q.appLE U V e).hom a) = (q.appLE U V' e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.appLE_map e (homOfLE h).op)

theorem appLE_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z) (hr : p ≫ q = r) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ q ⁻¹ᵁ U) (e₂ : W ≤ p ⁻¹ᵁ V) (e₃ : W ≤ r ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (p.appLE V W e₂).hom ((q.appLE U V e₁).hom a) = (r.appLE U W e₃).hom a := by
  subst hr
  exact congrArg (fun φ => CommRingCat.Hom.hom φ a) (Scheme.Hom.appLE_comp_appLE p q U V W e₁ e₂)

theorem valF_ne_zero_of_le {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens} (a : Γ(X, U))
    (hle : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a) : valF x U a ≠ 0 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := hle.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le a))
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  intro h0
  rw [e3, h0, map_zero, Scheme.basicOpen_zero] at hle
  exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem exists_point {X Y : Scheme.{0}} {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
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

theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (R : Type) [CommRing R] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (σ : SecAt G L χ), LocallyOfFiniteType G.hom → (∀ s : Sp R, ∃ z : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left z = s ∧ z ∈ nonzeroLocus σ) → ∃ s : LocSec G L χ.opensRange, IsLocSec s ∧ (∀ (K : Type) [Field K] (i : R →+* K), GenIs (spMap i ≫ χ) s (SecM.ofSec G (SecAt.pull G L σ i))) ∧ FibNz s χ.opensRange := by
  intro S G _ L R _ χ _ σ hft hnz
  let q : (Over.mk χ ⊗ G).left ⟶ G.left := (snd (Over.mk χ) G).left
  have hq : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion (pullback.snd χ G.hom))
  have ew : q ≫ G.hom = (fst (Over.mk χ) G).left ≫ χ :=
    (Over.w (snd (Over.mk χ) G)).trans (Over.w (fst (Over.mk χ) G)).symm
  have hN : ∀ y, G.hom (q y) ∈ χ.opensRange := fun y => by
    rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrange : G.hom ⁻¹ᵁ χ.opensRange ≤ q.opensRange := fun y hy =>
    (Scheme.Pullback.range_snd χ G.hom).ge hy
  have hle : ∀ j : Fin 1 → L.ι, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ≤
      q ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, hN y⟩
  have hbij : ∀ i : L.ι, Function.Bijective (q.appLE (L.U i ⊓ G.hom ⁻¹ᵁ χ.opensRange)
      ((LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U fun _ => i) (hle fun _ => i)).hom := fun i =>
    bij_appLE q _ (inf_le_right.trans hrange) _ _ fun y hy => Set.mem_iInter.2 fun _ => hy.1
  choose s hs using fun i : L.ι => (hbij i).2 (σ.f fun _ => i)
  have hs' : ∀ j : Fin 1 → L.ι, (q.appLE _ _ (hle j)).hom (s (j 0)) = σ.f j := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact hs i
  refine ⟨s, fun i j => ?_, fun K _ i => ⟨?_, funext fun j => ?_⟩, fun K _ _ x hx => ?_⟩
  · have hV : (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => i) ⊓ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => j) ≤
        q ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun y hy =>
      ⟨⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩, hN y⟩
    refine (bij_appLE q _ (inf_le_right.trans hrange) _ hV fun y hy =>
      ⟨Set.mem_iInter.2 fun _ => hy.1.1, Set.mem_iInter.2 fun _ => hy.1.2⟩).1 ?_
    have hc := σ.compat (fun _ => i) (fun _ => j)
    rw [← hs i, ← hs j] at hc
    rw [map_mul]
    refine (appLE_res q _ _ (inf_le_left.trans (hle fun _ => i)) _).trans
      (((res_appLE q _ _ _ _).symm.trans hc).trans (congrArg₂ (· * ·) ?_ ?_))
    · refine Eq.trans ?_ (appLE_res q _ _ (hV.trans (Scheme.Hom.preimage_mono _ inf_le_left)) _).symm
      simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    · exact (res_appLE q _ _ (inf_le_right.trans (hle fun _ => j)) _).trans (appLE_res q _ _ _ _).symm
  · rintro _ ⟨y, rfl⟩
    exact ⟨spMap i y, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · show genPull _ s j = (SecAt.pull G L σ i).f j
    unfold genPull SecAt.pull VVRank.pullS VVRank.pullTo
    dsimp only
    rw [← hs' j]
    exact (appLE_appLE _ q _ (VVRank.whisker_snd_left G _) _ _ _ _).symm
  · obtain ⟨s₀, hs₀⟩ : x (IsLocalRing.closedPoint K) ∈ χ.opensRange := hx ⟨_, rfl⟩
    obtain ⟨z, hz, hz'⟩ := hnz s₀
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    rw [← hs' j] at hj
    have hb := ((Scheme.basicOpen_appLE q _ _ (hle j) (s (j 0))).le hj).2
    obtain ⟨y, hy, hy'⟩ := exists_point G.hom x (G.left.basicOpen (s (j 0))) (q z) hb (by
      rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply, hz]
      exact hs₀)
    refine ⟨y, j 0, hy, ?_, valF_ne_zero_of_le _ hy'⟩
    rintro _ ⟨a, rfl⟩
    exact G.left.basicOpen_le (s (j 0)) (hy' (Set.mem_univ a))

end GlobalTheory.UMin.LocSecOfImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalThetaConstantsLocalisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThLocal
open GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtExist

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem exists_local : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) (R₁ : Type) [CommRing R₁] [Algebra R R₁] [IsNoetherianRing R₁] (N : ℕ) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Odd m → IsUnit (m : R) → PolFib G L g x → (∀ a, q a ^ (m ^ 2) = 1) → ∀ p : Ideal R₁, p.IsPrime → ∃ f ∉ p, ∃ c : Fin N → Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K) (a : Fin N) (pt : Over.mk (spMap ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap (j.comp (algebraMap R₁ (Localization.Away f))) ≫ (q a).left → ThG G L ρ m (SecAt.pull G L θ ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁))) pt (fn (j (c a))) := by
  intro S G _ _ L ρ hL hρ g m R _ _ x θ R₁ _ _ _ N q hm hmu hP hq p hp
  obtain ⟨P, α, -, hpb, w, hw⟩ := hP
  have hL₁ := P.isLB
  haveI := P.isAb.comm
  obtain ⟨ρ₁, hρ₁, hr⟩ := exists_rigidificationPullbackCompatibleIso hpb hw hL hL₁ hρ
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 (Sp R) P m
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  let T : Over (Sp R) := Over.mk (spMap (algebraMap R R₁))
  let T₁ : Over S := Over.mk (spMap (algebraMap R R₁) ≫ x)
  have hτ₁ : 𝟙 T.left ≫ T₁.hom = T.hom ≫ x := Category.id_comp _
  choose y hy hym using fun a => exists_torsion_down hpb (𝟙 T.left) (T₀ := T₁) hτ₁ (q a) (hq a)
  let pt₀ : T.left := (⟨p, hp⟩ : PrimeSpectrum R₁)
  choose V hV U hU using fun a => (sym (Sp R) P (m ^ 2) hm.pow T (y a) (hym a)).1 pt₀
  have hO : IsOpen (⋂ a, ((V a : T.left.Opens) : Set T.left)) := isOpen_iInter_of_finite fun a => (V a).2
  obtain ⟨_, ⟨f, rfl⟩, hf, hfO⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show pt₀ ∈ ⋂ a, ((V a : T.left.Opens) : Set T.left) from Set.mem_iInter.2 hV) hO
  refine ⟨f, hf, ?_⟩
  let Lf := Localization.Away f
  let af : R₁ →+* Lf := algebraMap R₁ Lf
  let i_f : R →+* Lf := af.comp (algebraMap R R₁)
  let Tf : Over (Sp R) := Over.mk (spMap i_f)
  let β : Tf ⟶ T := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) = spMap (af.comp (algebraMap R R₁))
    exact (spMap_comp _ _).symm)
  have hrange : ∀ a, Set.range (spMap af) ⊆ Set.range (V a).ι := by
    intro a
    rintro _ ⟨p', rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Set.mem_iInter.1 (hfO ((PrimeSpectrum.localization_away_comap_range Lf f).le ⟨p', rfl⟩)) a
  have hsym : ∀ a, ∃ θ' : ThetaGrp P.A P.L ((m : ℤ) ^ 2) Tf,
      SymLift P.A P.L ((m : ℤ) ^ 2) (m ^ 2) (β ≫ y a) θ' := by
    intro a
    let u := IsOpenImmersion.lift (V a).ι (spMap af) (hrange a)
    have hu : u ≫ (V a).ι = spMap af := IsOpenImmersion.lift_fac _ _ _
    let r : Tf ⟶ overRes (V a) := Over.homMk u (by
      show u ≫ (V a).ι ≫ T.hom = Tf.hom
      rw [← Category.assoc, hu]
      exact Over.w β)
    obtain ⟨θ', h'⟩ := GlobalLift.exists_symLift_pull hL₁ r (hU a)
    have e : r ≫ overResι (V a) = β := Over.OverMorphism.ext hu
    rw [← Category.assoc, e] at h'
    rw [← Nat.cast_pow]
    exact ⟨θ', h'⟩
  let T₀ : Over S := Over.mk (spMap i_f ≫ x)
  have hτ : 𝟙 Tf.left ≫ T₀.hom = Tf.hom ≫ x := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hpb (𝟙 Tf.left) (T₀ := T₀) hτ hw hL hL₁ (SecAt.pull G L θ i_f)
  have e₁ : (snd Tf P.A).left ≫ (mulA P.A m).left = (snd Tf P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨αf, hαf, -⟩ := exists_gen hL₁ (φ' := ![(snd Tf P.A).left, (snd Tf P.A ^ m).left]) (ε' := ![(m : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((m : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd Tf P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨τf, hτf, -⟩ := exists_gen hL₁ (φ' := fun _ : Fin 1 => (1 : Tf ⟶ P.A).left) (ε' := fun _ => (m : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ₁ (toUnit Tf).left) (m ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ₁ _) _)
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL₁ (mulT P.A Tf m) (snd Tf P.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 αf hαf th
  choose Uf hUf using hsym
  choose s₂ hs₂ using fun a => ThetaPtExist.exists_isTwistPull hL₁ (translT P.A (Uf a).pt) (translPt P.A (Uf a).pt)
    (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (Uf a).φ (Uf a).isGen s₁
  choose wv hwv using fun a => ThetaPtExist.exists_isValueAt hL₁ (s₂ a) 1 τf hτf
  have hyf : ∀ a, (β ≫ y a) ^ (m ^ 2) = 1 := fun a => by rw [← MonObj.comp_pow, hym a, MonObj.comp_one]
  obtain ⟨e, he⟩ := exists_thG hL₁ hρ₁ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hyf (th := th) (α := αf)
    hαf hτf hs₁ hUf hs₂ hwv
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a), ?_⟩
  intro K _ j a pt hpt
  clear hUf hs₂ hwv hs₁ sym hU hV hfO hO cg neg hG hrange
  let ξ : T₀ ⟶ T₁ := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) ≫ x = spMap (af.comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have hx₀ : 𝟙 Tf.left ≫ (ξ ≫ q a).left = (β ≫ y a).left ≫ α := by
    have h := hy a
    rw [Category.id_comp] at h
    rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ← h]
    rfl
  have hn₀ : (ξ ≫ q a) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, hq a, MonObj.comp_one]
  have up := ThG.up hpb (T := Tf) (T₀ := T₀) (𝟙 Tf.left) hτ hw hL hL₁ hr hx₀ hn₀ hth (he a)
  let δ : Over.mk (spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x) ⟶ T₀ := Over.homMk (spMap j) (by
    show spMap j ≫ spMap (af.comp (algebraMap R R₁)) ≫ x = spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have down := ThPull.thG_pull hL hρ δ up
  have ept : pt = δ ≫ ξ ≫ q a := by
    refine Over.OverMorphism.ext ?_
    rw [hpt, Over.comp_left, Over.comp_left, ← Category.assoc]
    exact congrArg (· ≫ (q a).left) (spMap_comp af j)
  have eθ : SecAt.pull G L θ ((j.comp af).comp (algebraMap R R₁)) = VVRank.pullS G _ δ (SecAt.pull G L θ i_f) := by
    unfold SecAt.pull
    rw [pullS_comp G hL]
    congr 1
    refine Over.OverMorphism.ext ?_
    exact spMap_comp i_f j
  have ec : δ.left.appTop.hom ((inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a)) =
      fn (j ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a))) := by
    have h1 : (inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a) =
        fn ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)) := by
      simp only [IsIso.inv_id, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply]
      exact ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom_inv_id_apply _).symm
    rw [h1]
    exact (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  rw [ept, eθ, ← ec]
  exact down

end GlobalTheory.UMin.ThLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preimage_of_local_preimages_injective : ∀ {X Y : Scheme.{0}} (a : Y ⟶ X), (∀ U : X.Opens, Function.Injective (a.app U).hom) → ∀ (V : X.Opens) {B : Type} (W : B → X.Opens), V ≤ ⨆ b, W b → ∀ (x : Γ(Y, a ⁻¹ᵁ V)), (∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) → ∃ y : Γ(X, V), (a.app V).hom y = x := by
  first | exact @GlobalTheory.Mum.imgLoc_exists | exact GlobalTheory.Mum.imgLoc_exists | (intros; apply GlobalTheory.Mum.imgLoc_exists <;> assumption)
end

