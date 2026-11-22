import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.Rigdesc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplication
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

theorem pt_of_fix {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G' : Over S}
    (N : Near π G') (φl : pullback G'.hom (pullback.fst π π) ⟶ pullback G'.hom (pullback.snd π π))
    (hfix : Desc.embL N _ (rfl : pullback.fst π π ≫ π = _) ≫ φl = Desc.embL N _ pullback.condition.symm)
    (T' : Scheme.{0}) (a : T' ⟶ N.U.left) (x : T' ⟶ pullback G'.hom (pullback.fst π π))
    (h : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) a (x ≫ pullback.fst G'.hom (pullback.fst π π))) :
    N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.snd π π) a (x ≫ φl ≫ pullback.fst G'.hom (pullback.snd π π)) := by
  obtain ⟨x₀, h1, h2, h3⟩ := h
  have hw : a ≫ N.U.hom = (x ≫ pullback.snd G'.hom (pullback.fst π π)) ≫ pullback.fst π π ≫ π := by
    calc a ≫ N.U.hom = x₀ ≫ pullback.snd N.U.hom π ≫ π := by
          rw [← h1, Category.assoc, pullback.condition]
      _ = (x ≫ pullback.snd G'.hom (pullback.fst π π)) ≫ pullback.fst π π ≫ π := by
          rw [reassoc_of% h2, Category.assoc]
  have hx₀ : pullback.lift a (x ≫ pullback.snd G'.hom (pullback.fst π π)) hw ≫
      Desc.toS N (pullback.fst π π) rfl = x₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Desc.toS, pullback.lift_fst, pullback.lift_fst, h1]
    · rw [Category.assoc, Desc.toS, pullback.lift_snd, pullback.lift_snd_assoc, h2, Category.assoc]
  have hx : pullback.lift a (x ≫ pullback.snd G'.hom (pullback.fst π π)) hw ≫
      Desc.embL N (pullback.fst π π) rfl = x := by
    apply pullback.hom_ext
    · rw [Category.assoc, Desc.embL, pullback.lift_fst, reassoc_of% hx₀, h3]
    · rw [Category.assoc, Desc.embL, pullback.lift_snd, pullback.lift_snd]
  have hφ : x ≫ φl = pullback.lift a (x ≫ pullback.snd G'.hom (pullback.fst π π)) hw ≫
      Desc.embL N (pullback.snd π π) pullback.condition.symm := by
    rw [← hfix, ← Category.assoc, hx]
  refine ⟨pullback.lift a (x ≫ pullback.snd G'.hom (pullback.fst π π)) hw ≫
      Desc.toS N (pullback.snd π π) pullback.condition.symm, ?_, ?_, ?_⟩
  · rw [Category.assoc, Desc.toS, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, Desc.toS, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc]
  · rw [reassoc_of% hφ, Desc.embL, pullback.lift_fst, Category.assoc]

theorem exists_datum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ φ, N.Datum φ := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hG N hL
  have h1 : pullback.fst π π ≫ π = pullback.fst π π ≫ π := rfl
  have h2 : pullback.snd π π ≫ π = pullback.fst π π ≫ π := pullback.condition.symm
  obtain ⟨fl1, su1, qc1⟩ := GlobalTheory.T.nearOpen_sumMap_flat_surjective_quasiCompact R hA S π hP hS hI G' hG N _ h1
  obtain ⟨fl2, su2, qc2⟩ := GlobalTheory.T.nearOpen_sumMap_flat_surjective_quasiCompact R hA S π hP hS hI G' hG N _ h2
  have e12 := GlobalTheory.T.kernelPair_sum_eq_of_sum_eq_other_pullback R hA S π hP hS hI G' hG N hL _ _ h1 h2
  have e21 := GlobalTheory.T.kernelPair_sum_eq_of_sum_eq_other_pullback R hA S π hP hS hI G' hG N hL _ _ h2 h1
  let f := EffectiveEpi.desc (Desc.sum N _ h1).left (Desc.sum N _ h2).left (fun g g' h => e12 _ g g' h)
  let g := EffectiveEpi.desc (Desc.sum N _ h2).left (Desc.sum N _ h1).left (fun g g' h => e21 _ g g' h)
  have hf : (Desc.sum N _ h1).left ≫ f = (Desc.sum N _ h2).left := EffectiveEpi.fac _ _ _
  have hg : (Desc.sum N _ h2).left ≫ g = (Desc.sum N _ h1).left := EffectiveEpi.fac _ _ _
  have wf : f ≫ ((Over.pullback (pullback.snd π π)).obj G').hom =
      ((Over.pullback (pullback.fst π π)).obj G').hom := by
    rw [← cancel_epi (Desc.sum N _ h1).left, reassoc_of% hf, Over.w, Over.w]
  have wg : g ≫ ((Over.pullback (pullback.fst π π)).obj G').hom =
      ((Over.pullback (pullback.snd π π)).obj G').hom := by
    rw [← cancel_epi (Desc.sum N _ h2).left, reassoc_of% hg, Over.w, Over.w]
  have hfg : f ≫ g = 𝟙 _ := by
    rw [← cancel_epi (Desc.sum N _ h1).left, reassoc_of% hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 _ := by
    rw [← cancel_epi (Desc.sum N _ h2).left, reassoc_of% hg, hf, Category.comp_id]
  have hs : Desc.sum N _ h1 ≫ Over.homMk f wf = Desc.sum N _ h2 := by
    apply Over.OverMorphism.ext
    exact hf
  have he := GlobalTheory.T.nearOpenEmbedding_comp_of_sumMap_comp R hA S π hP hS hI G' hG N hL _ _ h1 h2 (Over.homMk f wf) hs
  have hm := GlobalTheory.T.isMonHom_of_sumMap_comp_fixing_nearOpen R hA S π hP hS hI G' hG N _ _ h1 h2 (Over.homMk f wf) hs he
  refine ⟨⟨Over.homMk f wf, Over.homMk g wg, ?_, ?_⟩, hm, ?_⟩
  · apply Over.OverMorphism.ext
    exact hfg
  · apply Over.OverMorphism.ext
    exact hgf
  · intro T a x hx
    have hfix : Desc.embL N _ h1 ≫ f = Desc.embL N _ h2 := congrArg (fun k => k.left) he
    exact pt_of_fix N f hfix T a x hx

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMumfordBundleQuotient
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotDesc

def idq {S : Scheme.{0}} {A B : Over S} (q : A ⟶ B) : A ⊗ A ⟶ A ⊗ B := lift (fst A A) (snd A A ≫ q)

theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hΛ : (abelian₂ A L).IsLB)
    (a b : Y ⟶ A) : evc hΛ a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ, pull_lam, lift_fst,
    lift_snd]

theorem lam_mul_right_sub {S : Scheme.{0}} {A Y : Over S} [GrpObj A] [IsCommMonObj A] (c : Pic A.left)
    (a k y : Y ⟶ A) : lam c a (k * y) - lam c a y = lam c (a * y) k - lam c y k := by
  simp only [lam]
  rw [show a * y * k = a * (k * y) by rw [_root_.mul_assoc, _root_.mul_comm y k],
    show y * k = k * y from _root_.mul_comm y k]
  abel

theorem exists_descent_lam : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsMonHom i →
    Mono i → IsFinite H.hom → Flat H.hom →
    (∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x) →
    ∀ (B : Over (Sp R)) [GrpObj B] (q : A ⟶ B), IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left →
    Surjective q.left → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q →
    ∃ (P : LB (A ⊗ B).left) (hP : P.IsLB), ∀ (Y : Over (Sp R)) (a x : Y ⟶ A),
      evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) -
        GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
  intro R _ _ A _ hA L hL H _ i _ _ _ _ hK B _ q hB _ hqf hqfl hqs hpb
  have := hA.comm
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hku : lam (cls L hL) (fst A H) (snd A H ≫ i) = 0 := by
    rw [← evc_lam hL hΛ, ← triv_ev_iff hΛ]
    exact lam_triv_of_memKL _ A hA L hL H i ((hK H i).2 ⟨𝟙 H, Category.id_comp i⟩)
  have := hB.smooth
  have := hqf
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have hlfp : LocallyOfFinitePresentation q.left := inferInstance
  obtain ⟨-, h2⟩ := CompanionTheory.PfDual.rigDescent_holds (Sp R) A A B hA q hqfl hlfp hqs
  have hrig : Triv (ev (abelian₂ A L) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hΛ, evc_lam hL hΛ, lam_one_left]
  have hinv : ∀ (T : Over (Sp R)) (x x' : T ⟶ A), x ≫ q = x' ≫ q →
      LBIso (ev (abelian₂ A L) (fst A T) (snd A T ≫ x)) (ev (abelian₂ A L) (fst A T) (snd A T ≫ x')) := by
    intro T x x' hxx
    refine (cls_eq_iff (pull_isLB hΛ _) (pull_isLB hΛ _)).1 ?_
    rw [cls_ev hΛ, cls_ev hΛ, evc_lam hL hΛ, evc_lam hL hΛ]
    obtain ⟨z, hz1, hz2⟩ : ∃ z : T ⟶ H ⊗ A, z ≫ ((fst H A ≫ i) * snd H A) = x ∧ z ≫ snd H A = x' :=
      ⟨_, hpb.lift_fst x x' hxx, hpb.lift_snd x x' hxx⟩
    subst hz1 hz2
    have ex : snd A T ≫ z ≫ ((fst H A ≫ i) * snd H A) =
        (snd A T ≫ z ≫ fst H A ≫ i) * (snd A T ≫ z ≫ snd H A) := by
      rw [MonObj.comp_mul, MonObj.comp_mul]
    rw [ex, ← sub_eq_zero, lam_mul_right_sub]
    have k : ∀ u : A ⊗ T ⟶ A, lam (cls L hL) u (snd A T ≫ z ≫ fst H A ≫ i) = 0 := fun u => by
      have e := congrArg (GlobalTheory.CechPic.pull (lift u (snd A T ≫ z ≫ fst H A)).left) hku
      rwa [map_zero, pull_lam, lift_fst, lift_snd_assoc, Category.assoc, Category.assoc] at e
    rw [k, k, sub_zero]
  obtain ⟨N, hN, -, hiso⟩ := h2 (abelian₂ A L) hΛ hrig hinv
  refine ⟨N, hN, fun Y a x => ?_⟩
  have hPc : GlobalTheory.CechPic.pull (idq q).left (cls N hN) = cls (abelian₂ A L) hΛ :=
    ((cls_eq_iff hΛ (pull_isLB hN _)).2 hiso).symm
  have e : lift a (x ≫ q) = lift a x ≫ idq q := by
    simp [idq]
  rw [evc, e, Over.comp_left, pull_comp, hPc, show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ, pull_lam, lift_fst,
    lift_snd]
  rfl

end GlobalTheory.QuotDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenCoordinatesIdempotentRangeQuotientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenCoordinates_idempotentRange_quotient : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H]
  (σ : A →+* Module.End C H) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∀ (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, σ c x ∈ F) → (∀ x ∈ F, π x ∈ F) →
  (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
  (∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ F) ∧ d - ∑ i, w i ∈ F) →
  ∃ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) ∧
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) ∧
    (∀ k, y k ∈ LinearMap.range π) ∧ ∀ j k, ℓ j (y k) = if j = k then 1 else 0 := by
  first | exact @GlobalTheory.exists_eigen_coordinates_range_quot | exact GlobalTheory.exists_eigen_coordinates_range_quot | (intros; apply GlobalTheory.exists_eigen_coordinates_range_quot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_bijection_larger_closed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  first | exact @GlobalTheory.Mum.UpExt.exists_eqv_ext | exact GlobalTheory.Mum.UpExt.exists_eqv_ext | (intros; apply GlobalTheory.Mum.UpExt.exists_eqv_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantLiftFunctionalQuotientProjectivStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariantLift_functional_quotient_projective : ∀ {C : Type} [CommRing C] (I : Ideal C) {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (χ : A →+* C) (l₀ : H →ₗ[C] C ⧸ I), (∀ a x, l₀ (σ a x) = Ideal.Quotient.mk I (χ a) * l₀ x) →
  ∃ l : H →ₗ[C] C, (∀ a x, l (σ a x) = χ a * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = l₀ x := by
  first | exact @GlobalTheory.eqLift_tensorModOf | exact GlobalTheory.eqLift_tensorModOf | (intros; apply GlobalTheory.eqLift_tensorModOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalSymmetricBundleTranslateOrderTwStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_evenCubicalSymmetricBundle_translate_orderTwo : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P := by
  first | exact @GlobalTheory.MumTwistCP.exists_cp_transl | exact GlobalTheory.MumTwistCP.exists_cp_transl | (intros; apply GlobalTheory.MumTwistCP.exists_cp_transl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtLam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumExt

theorem exists_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ L : LB ((Over.pullback (jK R)).obj G).left, L.IsLB → ∃ PP : LB (G2 G).left, ExtLam G L PP := by
  intro R _ _ _ G _ _ hG L hL
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected
  obtain ⟨L', hL', hb⟩ := GlobalTheory.T.lineBundle_generic_fibre_extends_over_dvr R G L hL
  refine ⟨abelian₂ G L', DVR.linComb_isLB _ hL' _ _, fun κ₂ hκ => ?_⟩
  have h := isGrpPullback_pullback G (jK R)
  let V := lift (pushPt h.1.w (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
    (pushPt h.1.w (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
  have hV : V.left = κ₂ := by
    apply pullback.hom_ext
    · show (V ≫ fst G G).left = κ₂ ≫ (fst G G).left
      rw [hκ.1, lift_fst]
      rfl
    · show (V ≫ snd G G).left = κ₂ ≫ (snd G G).left
      rw [hκ.2, lift_snd]
      rfl
  have c := GlobalTheory.SymSpread.lbIso_cube h hL' hL hb (x2 G) (x2 _) V (fun i => by fin_cases i <;> simp [x2, V])
  rw [hV] at c
  exact c

end GlobalTheory.MumExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExternalTensorRigidifiedCubicalProduct
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.GrpBox

open GlobalTheory.SumDeg

theorem isBoxGen_extGen {X X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂)
    {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h₁ : Y ⟶ Y₁) (φ₁ : K → (Y₁ ⟶ X₁)) (e₁ : ∀ k, ψ k ≫ f₁ = h₁ ≫ φ₁ k) (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε))
    (h₂ : Y ⟶ Y₂) (φ₂ : K → (Y₂ ⟶ X₂)) (e₂ : ∀ k, ψ k ≫ f₂ = h₂ ≫ φ₂ k) (t₂ : LB.Gen (LB.LinComb L₂ φ₂ ε))
    (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) :
    IsBoxGen (CubePf.idIsoL (extLB L₁ L₂ f₁ f₂)) h₁ h₂ (extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂) t₁ t₂ := by
  intro Z r z J₁ J₂ J hJ₁ hJ₂ hJ
  have hE := good_ext (f₁ := f₁) (f₂ := f₂) hJ₁ hJ₂
  have key := gen_trans (isGen_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ ht₁ ht₂) r z (hE.mem ψ r) (hJ.mem ψ r)
  have k2 := gm_extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂ r z _ (hE.mem ψ r)
  rw [val_of t₁ (r ≫ h₁) z J₁ (fun k => J₁ ((r ≫ ψ k) ≫ f₁)) (fun k => by rw [Category.assoc, Category.assoc, e₁]),
    val_of t₂ (r ≫ h₂) z J₂ (fun k => J₂ ((r ≫ ψ k) ≫ f₂)) (fun k => by rw [Category.assoc, Category.assoc, e₂])]
  exact key.symm.trans k2

section Grp

variable {S : Scheme.{0}} {A A₁ A₂ : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A₁] [IsCommMonObj A₁]
  [GrpObj A₂] [IsCommMonObj A₂]

def pullCub (L : RigLB A₁) (c : CubicalStr A₁ L) (a : A ⟶ A₁) [IsMonHom a] :=
  CubePf.cubical (CubeMap.ofHom a) L c (LB.isLB_pull L.isLB _)
    (LBxP.isGen_pullAlong L.L a.left (𝟙 _) (fun _ : PUnit => eSec A₁) (fun _ => 1)
      (fun _ => eSec A) (fun _ => (CubeMap.ofHom a).e_comm) L.rig L.rigGen)

theorem exists_strBox (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsMonHom a₁] [IsMonHom a₂]
    (L₁ : RigLB A₁) (L₂ : RigLB A₂) (c₁ : CubicalStr A₁ L₁) (c₂ : CubicalStr A₂ L₂)
    (s₁ : SymGen A₁ L₁.L) (s₂ : SymGen A₂ L₂.L) (hs₁ : s₁.IsGen) (hs₂ : s₂.IsGen)
    (n₁ : LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec A₁)) (LB.oneGen L₁.L))
    (n₂ : LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec A₂)) (LB.oneGen L₂.L)) :
    ∃ (L : RigLB A) (c : CubicalStr A L) (s : SymGen A L.L)
      (w : LB.Iso L.L (extLB L₁.L L₂.L a₁.left a₂.left)), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L) ∧
      StrBox a₁ a₂ w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  have hL := isLB_extLB L₁.isLB L₂.isLB a₁.left a₂.left
  refine ⟨⟨extLB L₁.L L₂.L a₁.left a₂.left,
      extAt L₁.L L₂.L a₁.left a₂.left (eSec A) 1 _ (eSec_comp a₁) L₁.rig _ (eSec_comp a₂) L₂.rig, hL,
      isGen_extAt _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen⟩,
    tensCub (pullCub L₁ c₁ a₁) (pullCub L₂ c₂ a₂) _ hL _,
    extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂,
    CubePf.idIsoL _, isGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂, ?_, CubePf.idIsoL_isGen hL,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ L₁.rigGen L₂.rigGen,
    isBoxGen_extGen L₁.L L₂.L a₁.left a₂.left (thφ A (x3 A)) thε
      (a₁ ⊗ₘ a₁ ⊗ₘ a₁).left (thφ A₁ (x3 A₁)) (fun I => (CubeMap.ofHom a₁).psum_comm I.down) c₁.t
      (a₂ ⊗ₘ a₂ ⊗ₘ a₂).left (thφ A₂ (x3 A₂)) (fun I => (CubeMap.ofHom a₂).psum_comm I.down) c₂.t
      c₁.isGen c₂.isGen,
    isBoxGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂⟩
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at L₁.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at L₂.isLB y
  have o : eSec A ≫ (ι[A]).left = eSec A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[A] ≫ ι[A] = η[A])
  have v₁ : val s₁ (eSec A₁) y J₁ = 1 := by
    have v := val_corr hJ₁ n₁ (𝟙 _)
    rwa [val_pull hJ₁, Category.id_comp, val_one] at v
  have v₂ : val s₂ (eSec A₂) y J₂ = 1 := by
    have v := val_corr hJ₂ n₂ (𝟙 _)
    rwa [val_pull hJ₂, Category.id_comp, val_one] at v
  have e := (val_extGen L₁.L L₂.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) s₁ a₂.left _ (inv_comp a₂) s₂
    hs₁ hs₂ (eSec A) hJ hJ₁ hJ₂).trans (congrArg₂ (· * ·) (prod_sym (eSec A) _) rfl)
  rw [o, mul_inv_cancel, eSec_comp, eSec_comp, v₁, v₂, _root_.mul_one, _root_.mul_one] at e
  rw [val_pull hJ, Category.id_comp, val_one]
  exact e

end Grp

theorem exists_prod : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : RigLB G₁) (L₂ : RigLB G₂) (c₁ : CubicalStr G₁ L₁) (c₂ : CubicalStr G₂ L₂) (s₁ : SymGen G₁ L₁.L) (s₂ : SymGen G₂ L₂.L), s₁.IsGen → s₂.IsGen → LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec G₁)) (LB.oneGen L₁.L) → LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec G₂)) (LB.oneGen L₂.L) → ∃ (L : RigLB (G₁ ⊗ G₂)) (c : CubicalStr (G₁ ⊗ G₂) L) (s : SymGen (G₁ ⊗ G₂) L.L) (w : LB.Iso L.L (extLB L₁.L L₂.L (fst G₁ G₂).left (snd G₁ G₂).left)), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec (G₁ ⊗ G₂))) (LB.oneGen L.L) ∧ StrBox (fst G₁ G₂) (snd G₁ G₂) w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  intro S G₁ G₂ _ _ _ _ L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂
  exact exists_strBox (fst G₁ G₂) (snd G₁ G₂) L₁ L₂ c₁ c₂ s₁ s₂ hs₁ hs₂ n₁ n₂

end GlobalTheory.GrpBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvariety
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_factor_abelianSubvariety : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    ∃ (C : AbVar K) (p : A ⟶ C) (i : C ⟶ B), Surjective p.hom.left ∧ IsClosedImmersion i.hom.left ∧ p ≫ i = f := by
  intro K _ A B f
  obtain ⟨Z, p, i, hpi, hp, hi, hg⟩ := GlobalTheory.T.exists_geometricallyIntegral_image_of_hom K A B f
  obtain ⟨hG, hpm, him⟩ := GlobalTheory.T.exists_subgroupScheme_of_geometricallyIntegral_image K A B f Z p i hpi hp hi hg
  letI := hG
  have hmono : Mono i := by
    have : Mono i.left := inferInstance
    exact Over.mono_of_mono_left i
  have hcomm : IsCommMonObj Z := ⟨by
    apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  have hw : i.left ≫ B.X.hom = Z.hom := Over.w i
  have hB := B.ab
  have : Smooth B.X.hom := hB.smooth
  have : IsProper B.X.hom := hB.proper
  have hlft : LocallyOfFiniteType Z.hom := by rw [← hw]; infer_instance
  have hpr : IsProper Z.hom := by rw [← hw]; infer_instance
  have hsm : Smooth Z.hom := GlobalTheory.grpObj_smooth_of_geometricallyReduced K Z hlft inferInstance
  have hgc : GeometricallyConnected Z.hom := ⟨fun L _ y W fst snd h => by
    have : IsIntegral W := hg.geometrically_isIntegral y fst snd h
    infer_instance⟩
  have hab : IsAbelianScheme Z := ⟨hcomm, hsm, hpr, hgc⟩
  obtain ⟨g, hd⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K Z hab
  let C : AbVar K := { X := Z, ab := hab, dim := g, smooth := hd }
  refine ⟨C, Hom.mk (B := C) p, Hom.mk (A := C) i, hp, hi, ?_⟩
  exact hom_ext hpi

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtRationalTorsionUniformisedTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_rational_torsion_uniformised_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.Mum.Enlarge.exists_rational_ext | exact GlobalTheory.Mum.Enlarge.exists_rational_ext | (intros; apply GlobalTheory.Mum.Enlarge.exists_rational_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegularStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteModification_integral_elements_regular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens) (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) → (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S) (hgp : M'.gp ≫ h = M.gp), IsFinite h ∧ h ≫ M.π = M'.π ∧ ∀ m, ∃ c : Γ(M'.S, h ⁻¹ᵁ U m), (M'.gp.appLE (h ⁻¹ᵁ U m) (M.gp ⁻¹ᵁ U m) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U m))).hom c = b m := by
  first | exact @GlobalTheory.Mum.finiteModif_regular | exact GlobalTheory.Mum.finiteModif_regular | (intros; apply GlobalTheory.Mum.finiteModif_regular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusEndomorphismStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_endomorphism : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K), ∃ π : End A, IsFrob π ∧ (∀ x : A.X.left, (Hom.hom (A := A) (B := A) π).left x = x) ∧ ∀ (U : A.X.left.Opens) (h : U ≤ (Hom.hom (A := A) (B := A) π).left ⁻¹ᵁ U) (s : Γ(A.X.left, U)), ((Hom.hom (A := A) (B := A) π).left.appLE U U h).hom s = s ^ Fintype.card K := by
  first | exact @GlobalTheory.AV.FrobPow.exists_isFrob_pow | exact GlobalTheory.AV.FrobPow.exists_isFrob_pow | (intros; apply GlobalTheory.AV.FrobPow.exists_isFrob_pow; all_goals assumption)
end

