import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGluesFromCover
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmetricBundleDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem pull_pol : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (f : Sp R ⟶ Sp R₀) (A : PolAV (Sp R₀)) (G : Over (Sp R)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A f α → (A.L.pull α).IsLB ∧ Rigidified G (A.L.pull α) ∧ Sym G (A.L.pull α) ∧ RelAmple G (A.L.pull α) ∧ KTriv G (A.L.pull α) := by
  intro R R₀ _ _ f A G _ α hα
  have hw := (isGen_iff _).1 (GlobalTheory.UU.pullIso_isGen A.isLB α)
  exact ⟨pull_isLB A.isLB α, GlobalTheory.PolBaseChange.rigidified_pull hα A.rigid, GlobalTheory.PolBaseChange.sym_pull hα A.sym,
    relAmple_pull hα.1 A.isLB (pull_isLB A.isLB α) hw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample,
    kTriv_pull hα A.isLB (pull_isLB A.isLB α) hw A.ktriv⟩

theorem isSquare_unique : ∀ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (φ : G'.left ⟶ G.left) (φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left), IsSquare φ φ₂ → IsSquare φ φ₂' → φ₂ = φ₂' := by
  intro S S' G' G φ φ₂ φ₂' h h'
  have e : φ₂ ≫ (G ⊗ G).hom = φ₂' ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← Category.assoc, h.1, h'.1]
  let u : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let v : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' e.symm
  have : u = v := CartesianMonoidalCategory.hom_ext _ _
    (Over.OverMorphism.ext (by simpa [u, v] using h.1.trans h'.1.symm))
    (Over.OverMorphism.ext (by simpa [u, v] using h.2.trans h'.2.symm))
  exact congrArg (fun z => z.left) this
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate GlobalTheory.GtCoordCompare

theorem lbIso_diff_pull_pull : ∀ (X Y₁ Y₂ Z : Scheme.{0}) (M : LB X) (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) (u₁ v₁ : Y₁ ⟶ Y₁) (u₂ v₂ : Y₂ ⟶ Y₂) (q₁ : Z ⟶ Y₁) (q₂ : Z ⟶ Y₂), M.IsLB → q₁ ≫ u₁ ≫ g₁ = q₂ ≫ u₂ ≫ g₂ → q₁ ≫ v₁ ≫ g₁ = q₂ ≫ v₂ ≫ g₂ → LBIso ((LB.LinComb (M.pull g₁) (K := Fin 2) ![u₁, v₁] ![1, -1]).pull q₁) ((LB.LinComb (M.pull g₂) (K := Fin 2) ![u₂, v₂] ![1, -1]).pull q₂) := by
  intro X Y₁ Y₂ Z M g₁ g₂ u₁ v₁ u₂ v₂ q₁ q₂ hM hu hv
  refine lbIso_of_refines hM
    ((((refines_self (L := M) (fun _ : PUnit => g₁) (fun _ => 1)).linComb _ _)).linComb _ _)
    ((((refines_self (L := M) (fun _ : PUnit => g₂) (fun _ => 1)).linComb _ _)).linComb _ _) _ isGen_one
    fun U _ f => ?_
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, hu, hv]
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem transl_comp_eq : ∀ {S S₁ S₀ : Scheme.{0}} (G : Over S) (G₁ : Over S₁) (A : Over S₀) [GrpObj G] [GrpObj G₁] [GrpObj A] (f : S ⟶ S₀) (f₁ : S₁ ⟶ S₀) (φ : G.left ⟶ A.left) (φ₁ : G₁.left ⟶ A.left), IsGrpPullback G A f φ → IsGrpPullback G₁ A f₁ φ₁ → ∀ (x : 𝟙_ (Over S) ⟶ G) (t : 𝟙_ (Over S₁) ⟶ G₁) (Z : Scheme.{0}) (q : Z ⟶ G.left) (q₁ : Z ⟶ G₁.left), q ≫ φ = q₁ ≫ φ₁ → q ≫ (toUnit G ≫ x).left ≫ φ = q₁ ≫ (toUnit G₁ ≫ t).left ≫ φ₁ → q ≫ (GlobalTheory.PolTranslate.transl x).left ≫ φ = q₁ ≫ (GlobalTheory.PolTranslate.transl t).left ≫ φ₁ := by
  intro S S₁ S₀ G G₁ A _ _ _ f f₁ φ φ₁ h h₁ x t Z q q₁ e ec
  let T : Over S := Over.mk (q ≫ G.hom)
  let T₁ : Over S₁ := Over.mk (q₁ ≫ G₁.hom)
  let a : T ⟶ G := Over.homMk q rfl
  let a₁ : T₁ ⟶ G₁ := Over.homMk q₁ rfl
  have k : q ≫ (GlobalTheory.PolTranslate.transl x).left = (a * (toUnit T ≫ x)).left := comp_transl_left a x
  have k₁ : q₁ ≫ (GlobalTheory.PolTranslate.transl t).left = (a₁ * (toUnit T₁ ≫ t)).left := comp_transl_left a₁ t
  have hw : (q ≫ G.hom) ≫ f = (q₁ ≫ G₁.hom) ≫ f₁ := by
    rw [Category.assoc, Category.assoc, ← h.1.w, ← h₁.1.w, ← Category.assoc, ← Category.assoc, e]
  let x₀ : Over.mk (T.hom ≫ f) ⟶ A := Over.homMk (a.left ≫ φ) (by
    show (q ≫ φ) ≫ A.hom = (q ≫ G.hom) ≫ f
    rw [Category.assoc, h.1.w, Category.assoc])
  let y₀ : Over.mk (T.hom ≫ f) ⟶ A := Over.homMk ((toUnit T ≫ x).left ≫ φ) (by
    show ((toUnit T ≫ x).left ≫ φ) ≫ A.hom = (q ≫ G.hom) ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w (toUnit T ≫ x)]
    rfl)
  let x₁ : Over.mk (T₁.hom ≫ f₁) ⟶ A := Over.homMk (a₁.left ≫ φ₁) (by
    show (q₁ ≫ φ₁) ≫ A.hom = (q₁ ≫ G₁.hom) ≫ f₁
    rw [Category.assoc, h₁.1.w, Category.assoc])
  let y₁ : Over.mk (T₁.hom ≫ f₁) ⟶ A := Over.homMk ((toUnit T₁ ≫ t).left ≫ φ₁) (by
    show ((toUnit T₁ ≫ t).left ≫ φ₁) ≫ A.hom = (q₁ ≫ G₁.hom) ≫ f₁
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w (toUnit T₁ ≫ t)]
    rfl)
  have E := h.2 T a (toUnit T ≫ x) x₀ y₀ rfl rfl
  have E₁ := h₁.2 T₁ a₁ (toUnit T₁ ≫ t) x₁ y₁ rfl rfl
  let j : Over.mk (T.hom ≫ f) ⟶ Over.mk (T₁.hom ≫ f₁) := Over.homMk (𝟙 Z) (by
    show 𝟙 Z ≫ (q₁ ≫ G₁.hom) ≫ f₁ = (q ≫ G.hom) ≫ f
    rw [Category.id_comp, hw])
  have hx : j ≫ x₁ = x₀ := Over.OverMorphism.ext (by
    show 𝟙 Z ≫ q₁ ≫ φ₁ = q ≫ φ
    rw [Category.id_comp, e])
  have hy : j ≫ y₁ = y₀ := Over.OverMorphism.ext (by
    show 𝟙 Z ≫ (toUnit T₁ ≫ t).left ≫ φ₁ = (toUnit T ≫ x).left ≫ φ
    have k2 : (toUnit T ≫ x).left = q ≫ (toUnit G ≫ x).left := by
      simp only [Over.comp_left]
      show (q ≫ G.hom) ≫ x.left = q ≫ (G.hom ≫ x.left)
      rw [Category.assoc]
    have k3 : (toUnit T₁ ≫ t).left = q₁ ≫ (toUnit G₁ ≫ t).left := by
      simp only [Over.comp_left]
      show (q₁ ≫ G₁.hom) ≫ t.left = q₁ ≫ (G₁.hom ≫ t.left)
      rw [Category.assoc]
    rw [Category.id_comp, k2, k3, Category.assoc, Category.assoc]
    exact ec.symm)
  have H := congrArg (fun z => z.left) (MonObj.comp_mul j x₁ y₁)
  rw [hx, hy] at H
  rw [← Category.assoc, ← Category.assoc, k, k₁, ← E, ← E₁, ← H]
  exact Category.id_comp _
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem lam_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId L) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L (𝟙 X) (𝟙 X) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

theorem exists_finite_ext : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (A' : PolAV (Sp Ω)) (α : A'.A.left ⟶ A.A.left) (α₂ : (G2 A'.A).left ⟶ (G2 A.A).left), IsGrpPullback A'.A A.A (spMap ga) α → Geo.Tor.IsSquare α α₂ → LBIso (abelian₂ A'.A A'.L) ((abelian₂ A.A A.L).pull α₂) → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (p : pullback A'.A.hom (spMap j) ⟶ A₁.A.left), io.Finite ∧ l.comp io = j.comp ga ∧ IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ Geo.Tor.IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ p ≫ α₁ = pullback.fst _ _ ≫ α ∧ p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l ∧ LBIso (A'.L.pull (pullback.fst A'.A.hom (spMap j))) (A₁.L.pull p) := by
  intro K Ω _ _ _ ga A A' α α₂ hα hsq hΛ
  have := A.isAb.comm
  have := A'.isAb.comm
  obtain ⟨hLB, hrig, hsym, hamp, hK⟩ := pull_pol Ω K (spMap ga) A A'.A α hα
  let P : PolAV (Sp Ω) := ⟨A'.A, A'.isAb, A'.g, A'.smoothDim, A.L.pull α, hLB, hrig, hsym, hamp, hK⟩
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  obtain ⟨β₂, hβ, hT⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ga) A.A A'.A α hα
  have e₁ := hT A.L (A.L.pull α) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hLB hΛA (GlobalTheory.PolBaseChange.lbIso_refl hLB)
    (lam_pull_id hΛA)
  rw [Category.comp_id, isSquare_unique α β₂ α₂ hβ hsq] at e₁
  have hΛ' : LBIso (abelian₂ P.A A'.L) (abelian₂ P.A P.L) :=
    LBIso.trans (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB hΛA _) (DVR.linComb_isLB _ hLB _ _) hΛ e₁.symm
  obtain ⟨x, hx2, hxL⟩ := GlobalTheory.T.exists_twoTorsion_rigidTranslate_same_mumfordBundle Ω P A'.L A'.isLB A'.rigid A'.sym hΛ'
  obtain ⟨K', _, io, l, y, hfin, hcomp, hy2, hy⟩ := GlobalTheory.T.exists_finite_ext_twoTorsion_point_abelianVariety K Ω ga A A'.A α hα x hx2
  obtain ⟨A₁, α₁, α₁₂, t, hα₁, hsq₁, hΛ₁, ht, hL₁⟩ := GlobalTheory.T.exists_baseChange_polarisation_translate_two_torsion K K' io A y hy2
  have hid : spMap (RingHom.id Ω) = 𝟙 _ := Spec.map_id _
  have w : (pullback.fst A'.A.hom (spMap (RingHom.id Ω)) ≫ α) ≫ A.A.hom =
      (pullback.snd A'.A.hom (spMap (RingHom.id Ω)) ≫ spMap l) ≫ spMap io := by
    rw [Category.assoc, hα.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc]
    congr 1
    rw [← hcomp, hid, Category.id_comp]
    show Spec.map (CommRingCat.ofHom (l.comp io)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let p := hα₁.1.lift _ _ w
  have hp1 : p ≫ α₁ = pullback.fst _ _ ≫ α := hα₁.1.lift_fst _ _ _
  have hp2 : p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l := hα₁.1.lift_snd _ _ _
  refine ⟨K', inferInstance, io, Ω, inferInstance, RingHom.id Ω, l, A₁, α₁, α₁₂, p, hfin, by rw [hcomp]; rfl,
    hα₁, hsq₁, hΛ₁, hp1, hp2, ?_⟩
  have hc : pullback.fst A'.A.hom (spMap (RingHom.id Ω)) ≫ (toUnit A'.A ≫ x).left ≫ α =
      p ≫ (toUnit A₁.A ≫ t).left ≫ α₁ := by
    have hsnd : pullback.snd A'.A.hom (spMap (RingHom.id Ω)) ≫ spMap (RingHom.id Ω) = pullback.snd _ _ := by
      rw [hid, Category.comp_id]
    show pullback.fst _ _ ≫ (A'.A.hom ≫ x.left) ≫ α = p ≫ (A₁.A.hom ≫ t.left) ≫ α₁
    rw [Category.assoc, ← Category.assoc (pullback.fst _ _), pullback.condition, hsnd, Category.assoc,
      ← Category.assoc p, hp2, Category.assoc, ht, hy]
  have htr := transl_comp_eq A'.A A₁.A A.A (spMap ga) (spMap io) α α₁ hα hα₁ x t _ _ p hp1.symm hc
  have hE := lbIso_diff_pull_pull _ _ _ _ A.L α α₁ _ _ _ _ (pullback.fst A'.A.hom (spMap (RingHom.id Ω))) p A.isLB
    htr hc
  have hR₁ : (rigTransl (A.L.pull α₁) t).IsLB := DVR.linComb_isLB _ (pull_isLB A.isLB _) _ _
  have hR : (rigTransl (A.L.pull α) x).IsLB := DVR.linComb_isLB _ (pull_isLB A.isLB _) _ _
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB hR _) (pull_isLB A₁.isLB _) (GlobalTheory.RigidBundleGlue.LBIso.pull hxL _)
    (LBIso.trans (pull_isLB hR _) (pull_isLB hR₁ _) (pull_isLB A₁.isLB _) hE (GlobalTheory.RigidBundleGlue.LBIso.pull hL₁.symm _))

end GlobalTheory.SymFinExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteLocalExtensionFractionRingOfGaloisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteLocalExtension_fractionRing_of_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [Algebra (FractionRing R) E], FiniteDimensional (FractionRing R) E → IsGalois (FractionRing R) E → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (t : E →+* FractionRing R'), FinExt ρ ∧ ∀ r : R, t (algebraMap (FractionRing R) E (algebraMap R (FractionRing R) r)) = algebraMap R' (FractionRing R') (ρ r) := by
  first | exact @GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois | exact GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois | (intros; apply GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepresentingLinearLevelsAbelianSchemStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_representing_linearLevels_abelianScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH], IsAbelianScheme AH → IsUnit ((N : ℕ) : Γ(H, ⊤)) → ∀ (actH : OActN D.O AH), ∃ (E : Scheme.{0}) (πE : E ⟶ H) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsFinite πE ∧ IsGrpPullback AE AH πE φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_linLevel) | (exact GlobalTheory.UPel.HT.exists_finite_rep_linLevel) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_linLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSurjectiveCoverFromOpensStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_surjective_cover_from_opens : ∀ (X Z : Scheme.{0}) (i : X ⟶ Z) (T : Type) [Finite T] (M : T → Scheme.{0}) (U : T → Z.Opens) (g : ∀ t, M t ⟶ (U t).toScheme), (∀ t, IsFinite (g t)) → (∀ t, Set.range i ⊆ (U t : Set Z)) → (∀ x : X, ∃ (t : T) (w : M t), (g t ≫ (U t).ι) w ⤳ i x) → ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (yM : Sp K ⟶ M t), yM ≫ g t ≫ (U t).ι = y' ≫ q ≫ i := by
  first | exact @GlobalTheory.FinCover.exists_finite_surjective_cover | exact GlobalTheory.FinCover.exists_finite_surjective_cover | (intros; apply GlobalTheory.FinCover.exists_finite_surjective_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetPowSmulMem
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FinitePowerAnnihilation

theorem exists_finset_pow_smul_mem {R A Rf Af : Type} [CommRing R] [CommRing A] [CommRing Rf] [CommRing Af]
    [IsNoetherianRing R] [Algebra R A] [Algebra R Rf] (f : R) [IsLocalization.Away f Rf]
    (ψ : Rf →+* Af) (ρ : A →+* Af) (hc : ∀ a, ρ (algebraMap R A a) = ψ (algebraMap R Rf a))
    (hk : ∀ x, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0) (T : Set Af) (hT : T.Finite)
    (hI : ∀ y ∈ T, ψ.IsIntegralElem y) (M : Set A)
    (hM : ∀ x ∈ M, ρ x ∈ Subring.closure (Set.range ψ ∪ T)) :
    ∃ s : Finset A, (s : Set A) ⊆ M ∧ ∀ x ∈ M, ∃ n : ℕ, f ^ n • x ∈ Submodule.span R (s : Set A) := by
  classical
  letI : Algebra Rf Af := ψ.toAlgebra
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers f) Rf inferInstance
  have hfg : (Algebra.adjoin Rf T).toSubmodule.FG := fg_adjoin_of_finite hT hI
  have hle : Submodule.span Rf (ρ '' M) ≤ (Algebra.adjoin Rf T).toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h := hM x hx
    have : Subring.closure (Set.range ψ ∪ T) ≤ (Algebra.adjoin Rf T).toSubring := by
      rw [Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact (Algebra.adjoin Rf T).algebraMap_mem a
      · exact Algebra.subset_adjoin hy
    exact this h
  have hfg2 : (Submodule.span Rf (ρ '' M)).FG := hfg.of_le hle
  obtain ⟨u, hu, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg2
  obtain ⟨s, hs, hsu⟩ := Finset.subset_set_image_iff.1 hu
  refine ⟨s, hs, fun x hx => ?_⟩
  have hx1 : ρ x ∈ Submodule.span Rf (u : Set Af) := hsp ▸ Submodule.subset_span ⟨x, hx, rfl⟩
  have key : ∀ z ∈ Submodule.span Rf (u : Set Af), ∃ n : ℕ, ∃ w ∈ Submodule.span R (s : Set A),
      ρ w = ρ (algebraMap R A f) ^ n * z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rw [← hsu, Finset.coe_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨0, w, Submodule.subset_span hw, by simp⟩
    | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨n, w, hw, e⟩ := ha
      obtain ⟨m, v, hv, e'⟩ := hb
      refine ⟨n + m, f ^ m • w + f ^ n • v,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hv), ?_⟩
      simp only [Algebra.smul_def, map_add, map_mul, map_pow, e, e']
      ring
    | smul c a _ ha =>
      obtain ⟨n, w, hw, e⟩ := ha
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers f) c
      refine ⟨n + k, b • w, Submodule.smul_mem _ _ hw, ?_⟩
      have hb' : ψ c * ρ (algebraMap R A f) ^ k = ρ (algebraMap R A b) := by
        rw [hc, hc, ← map_pow, ← map_mul, ← map_pow]
        exact congrArg ψ hb
      have hs' : c • a = ψ c * a := rfl
      rw [Algebra.smul_def, map_mul, e, ← hb', hs']
      ring
  obtain ⟨n, w, hw, e⟩ := key _ hx1
  obtain ⟨m, hm⟩ := hk (f ^ n • x - w) (by rw [map_sub, e, Algebra.smul_def, map_mul, map_pow, map_pow, sub_self])
  refine ⟨m + n, ?_⟩
  rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add] at hm
  rw [hm]
  exact Submodule.smul_mem _ _ hw

theorem pow_mul_eq_zero_of_res {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) (W : S.Opens) (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ W)) (hx : resK gp (S.basicOpen_le f) x = 0) :
    ∃ n : ℕ, (gp.app W).hom f ^ n * x = 0 := by
  have hc : IsCompact ((gp ⁻¹ᵁ W : (Sp K).Opens) : Set (Sp K)) :=
    (Set.subsingleton_of_subsingleton (α := PrimeSpectrum K)).isCompact
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (Sp K) hc x ((gp.app W).hom f) ?_
  have e : (Sp K).basicOpen ((gp.app W).hom f) ≤ gp ⁻¹ᵁ S.basicOpen f := (Scheme.preimage_basicOpen gp f).ge
  have h := congrArg ((Sp K).presheaf.map (homOfLE e).op).hom hx
  rw [map_zero, resK, ← CommRingCat.comp_apply, ← Functor.map_comp] at h
  exact h

theorem finFam_finite {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ}
    (V : Fin r → S.Opens) (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (hV : ⨆ i, V i = ⊤)
    (ht : ∀ i, ∀ y ∈ t i, (gp.app (V i)).hom.IsIntegralElem y) (W : S.Opens) (hW : IsAffineOpen W) :
    ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W), (∀ y ∈ s, y ∈ finFam gp V t W) ∧
      ∀ x ∈ finFam gp V t W, ∃ c : Γ(Sp K, gp ⁻¹ᵁ W) → Γ(S, W), x = ∑ y ∈ s, (gp.app W).hom (c y) * y := by
  classical
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  letI : Algebra Γ(S, W) Γ(Sp K, gp ⁻¹ᵁ W) := (gp.app W).hom.toAlgebra
  have loc : ∀ f : Γ(S, W), (∃ i, S.basicOpen f ≤ V i) → ∃ s : Finset Γ(Sp K, gp ⁻¹ᵁ W),
      (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) ⊆ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)) ∧
      ∀ x ∈ (finFam gp V t W : Set Γ(Sp K, gp ⁻¹ᵁ W)), ∃ n : ℕ,
        f ^ n • x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) := by
    rintro f ⟨i, hi⟩
    haveI := hW.isLocalization_basicOpen f
    refine exists_finset_pow_smul_mem (Rf := Γ(S, S.basicOpen f)) f (gp.app (S.basicOpen f)).hom
      (resK gp (S.basicOpen_le f)) (fun a => resK_app gp _ a) ?_ (resK gp hi '' (t i : Set _))
      ((t i).finite_toSet.image _) ?_ _ ?_
    · intro x hx
      obtain ⟨n, hn⟩ := pow_mul_eq_zero_of_res gp W f x hx
      exact ⟨n, by rw [Algebra.smul_def, map_pow]; exact hn⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hp0⟩ := ht i y hy
      refine ⟨p.map (S.presheaf.map (homOfLE hi).op).hom, hp.map _, ?_⟩
      have e : (gp.app (S.basicOpen f)).hom.comp (S.presheaf.map (homOfLE hi).op).hom =
          (resK gp hi).comp (gp.app (V i)).hom := RingHom.ext fun a => (resK_app gp hi a).symm
      rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hp0, map_zero]
    · intro x hx
      have hii : S.basicOpen f ≤ W ⊓ V i := le_inf (S.basicOpen_le f) hi
      have h1 := (mem_finFam gp V t W x).1 hx i
      have hm : resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) ∈ (Subring.closure _).map (resK gp hii) :=
        ⟨_, h1, rfl⟩
      rw [RingHom.map_closure, resK_resK] at hm
      refine Subring.closure_mono ?_ hm
      rintro _ ⟨y, ⟨a, rfl⟩ | ⟨z, hz, rfl⟩, rfl⟩
      · exact Or.inl ⟨_, (resK_app gp hii a).symm⟩
      · exact Or.inr ⟨z, hz, by rw [resK_resK]⟩
  have hspan : Ideal.span {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i} = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    have hx2 : x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx2
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le ⟨x, hi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, hf⟩, hxf⟩
  obtain ⟨F, hF, hFs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    {f : Γ(S, W) | ∃ i, S.basicOpen f ≤ V i}).1
    (IsNoetherian.noetherian (R := Γ(S, W)) _)
  have hF1 : Ideal.span (F : Set Γ(S, W)) = ⊤ := hFs.symm.trans hspan
  choose σ hσ using loc
  let s : Finset Γ(Sp K, gp ⁻¹ᵁ W) := F.attach.biUnion fun f => σ f.1 (hF f.2)
  refine ⟨s, fun y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨f, -, hf⟩ := Finset.mem_biUnion.1 hy
    exact (hσ f.1 (hF f.2)).1 hf
  · have hxs : x ∈ Submodule.span Γ(S, W) (s : Set Γ(Sp K, gp ⁻¹ᵁ W)) := by
      refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (F : Set Γ(S, W)) hF1 x fun f => ?_
      obtain ⟨n, hn⟩ := (hσ f.1 (hF f.2)).2 x hx
      refine ⟨n, Submodule.span_mono ?_ hn⟩
      intro y hy
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨⟨f.1, f.2⟩, Finset.mem_attach _ _, hy⟩)
    obtain ⟨c, hc⟩ := Submodule.mem_span_finset.1 hxs
    exact ⟨c, hc.2.symm⟩

end GlobalTheory.FinitePowerAnnihilation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagSpannedFrame
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

theorem freeMap_app_freeFrame {X : Scheme.{0}} {I J : Type} (f : I → J) (i : I) :
    Scheme.Modules.Hom.app (M := GlobalTheory.QCoh.freeModule X I) (N := GlobalTheory.QCoh.freeModule X J)
      (SheafOfModules.freeMap (R := X.ringCatSheaf) f) ⊤ (freeFrame X I i) = freeFrame X J (f i) := by
  refine (GlobalTheory.QCoh.app_app (M := structureModule X) (N := GlobalTheory.QCoh.freeModule X I)
    (P := GlobalTheory.QCoh.freeModule X J) (SheafOfModules.ιFree i) (SheafOfModules.freeMap f) ⊤ (show Γ(structureModule X, ⊤) from (1 : Γ(X, ⊤)))).trans ?_
  unfold freeFrame
  congr 2
  exact congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) (SheafOfModules.ιFree_freeMap (R := X.ringCatSheaf) f i)

theorem exists_flag_spans_of_frame : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (v : Fin m → Γ(F, ⊤)),
    IsFrame v → ∃ fl : Vert.Flag F m, Spans fl ⊤ v := by
  intro X F m v hv
  refine ⟨(GlobalTheory.FlagSurj.freeFlag X m).ofIso ((isFrame_freeFrame X (Fin m)).iso hv), fun l => ?_⟩
  refine ⟨freeFrame X (Fin l), isFrame_freeFrame X (Fin l), fun j => ?_⟩
  refine (GlobalTheory.QCoh.app_app (M := GlobalTheory.QCoh.freeModule X (Fin l)) (N := GlobalTheory.QCoh.freeModule X (Fin m)) (P := F)
    (SheafOfModules.freeMap (R := X.ringCatSheaf) (Fin.castLE (Nat.lt_succ_iff.mp l.2)))
    ((isFrame_freeFrame X (Fin m)).iso hv).hom ⊤ (freeFrame X (Fin l) j)).symm.trans ?_
  rw [freeMap_app_freeFrame, IsFrame.iso_hom_app]

end GlobalTheory.FlagCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatChartEtaleOfQuasiFiniteAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → (∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ Etale (W.ι ≫ pullback.snd τ h) := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxc hxm hinj hsurj hqf
  have hτf : LocallyOfFiniteType τ := by
    have : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUf
    exact locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have hτs : IsSeparated τ := by
    have : IsSeparated (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUs
    exact IsSeparated.of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have : IsNoetherianRing R := hR.1
  have hA : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  obtain ⟨T, h, W, p, het, hcon, hpW, hpx, hfin, hone, hgeo⟩ := GlobalTheory.T.exists_etale_neighbourhood_finite_piece_isolated_point _ _ τ hA hτf hτs x hqf
  have hiso := GlobalTheory.T.isIso_finite_piece_flat_connected_chart R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxm hinj hsurj
    T h W p inferInstance hcon hpW hpx hfin hone hgeo
  exact ⟨T, h, W, p, inferInstance, hpW, hpx, inferInstance⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateGenericBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisConjugate_genericBundle_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (hβ : β ≫ G.hom = G'.hom ≫ spMap ρ), (∀ σ, a.act σ ≫ β = β) → ∀ σ : Gal ρ, ∃ ψ : pullback G'.hom (jK R') ⟶ pullback G'.hom (jK R'), ψ ≫ genMap hρ β hβ = genMap hρ β hβ ∧ ψ ≫ pullback.snd G'.hom (jK R') = pullback.snd G'.hom (jK R') ≫ spMap (fracAut σ.1).toRingHom ∧ LBIso (U'.LG.L.pull (pullback.fst G'.hom (jK R'))) ((U'.LG.L.pull (pullback.fst G'.hom (jK R'))).pull ψ) := by
  first | exact @GlobalTheory.Mum.GenDesc.exists_inv | exact GlobalTheory.Mum.GenDesc.exists_inv | (intros; apply GlobalTheory.Mum.GenDesc.exists_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens), (∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) → ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  first | exact @GlobalTheory.Mum.exists_gen_of_cubeTen | exact GlobalTheory.Mum.exists_gen_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_gen_of_cubeTen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransferThroughTensorIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_transfer_through_tensorIso : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) {Y : Scheme.{0}} {K : Type} [Fintype K] (φ' : K → (Y ⟶ D'.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L (fun p : K × ((Fin r × Fin r) × Fin 4) => φ' p.1 ≫ tensφ T.pr p.2) (fun p => ε p.1 * tensε W p.2))), t.IsGen → ∃ t' : LB.Gen (LB.LinComb D'.P.L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → (∏ a, gm (q ≫ φ' a) z _ (T.w.s (fun k => J ((q ≫ φ' a) ≫ tensφ T.pr k), J' (q ≫ φ' a))) ^ ε a) * val t' q z J' = val t q z J := by
  first | exact @GlobalTheory.TensGen.exists_gen_transfer | exact GlobalTheory.TensGen.exists_gen_transfer | (intros; apply GlobalTheory.TensGen.exists_gen_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointFactorOfInjectiveBaseMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoint_factor_of_injective_base_map : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ ξ : Sp W ⟶ M.S, ξ ≫ M.π = spMap φ → ∃ ψ : FractionRing R →+* FractionRing W, ψ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ ∧ spMap ψ ≫ M.gp = jK W ≫ ξ := by
  first | exact @GlobalTheory.Mum.Modif.exists_generic_factor | exact GlobalTheory.Mum.Modif.exists_generic_factor | (intros; apply GlobalTheory.Mum.Modif.exists_generic_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueCopiesOfSchemeCocycleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_copies_of_scheme_cocycle : ∀ (Y : Scheme.{0}) (J : Type) (V : J → J → Y.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ Y), (∀ i, V i i = ⊤) → (∀ i, τ i i = (V i i).ι) → (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) → (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) → ∃ (G : Scheme.{0}) (ψ : J → (Y ⟶ G)), (∀ j, IsOpenImmersion (ψ j)) ∧ (∀ g : G, ∃ j, g ∈ Set.range (ψ j)) ∧ (∀ i j, IsPullback (V i j).ι (τ i j) (ψ i) (ψ j)) ∧ ∀ (Z : Scheme.{0}) (g : J → (Y ⟶ Z)), (∀ i j, (V i j).ι ≫ g i = τ i j ≫ g j) → ∃ F : G ⟶ Z, ∀ j, ψ j ≫ F = g j := by
  first | exact @GlobalTheory.GlueCopies.exists_glue_copies | exact GlobalTheory.GlueCopies.exists_glue_copies | (intros; apply GlobalTheory.GlueCopies.exists_glue_copies <;> assumption)
end

