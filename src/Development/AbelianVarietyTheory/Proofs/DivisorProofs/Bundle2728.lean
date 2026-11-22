import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WAddLeMax
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SecMoveK
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutomorphismActsOnDeeperLevelLabelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_automorphism_acts_on_deeper_level_labels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  first | exact @GlobalTheory.Poinc.GalAct.exists_galLab | exact GlobalTheory.Poinc.GalAct.exists_galLab | (intros; apply GlobalTheory.Poinc.GalAct.exists_galLab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_invariant_functions_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y → IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) → (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ V : Y.Opens, Function.Injective (β.app V).hom ∧ ∀ u : Γ(Y', β ⁻¹ᵁ V), (∀ σ (h : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (β.app V).hom := by
  first | exact @GlobalTheory.Mum.InvFun.invariant_functions | exact GlobalTheory.Mum.InvFun.invariant_functions | (intros; apply GlobalTheory.Mum.InvFun.invariant_functions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariantsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisQuotient_affineOpen_spec_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ V : X.left.Opens, IsAffineOpen V → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra R C') (_ : Algebra R' C') (_ : IsScalarTower R R' C') (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (C : Subalgebra R C') (j : Sp C' ⟶ H.toScheme) (l : Sp C ⟶ X.left), IsOpenImmersion j ∧ IsOpenImmersion l ∧ Set.range l = (V : Set X.left) ∧ IsPullback j (spMap (algebraMap C C')) π l ∧ j ≫ H.ι ≫ G'.hom = spMap (algebraMap R' C') ∧ l ≫ X.hom = spMap (algebraMap R C) ∧ (∀ σ, spMap (actC σ : C' →+* C') ≫ j ≫ H.ι = j ≫ H.ι ≫ act σ) ∧ (∀ σ r, actC σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) ∧ ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := by
  first | exact @GlobalTheory.Mum.quot_affine_spec_invariants | exact GlobalTheory.Mum.quot_affine_spec_invariants | (intros; apply GlobalTheory.Mum.quot_affine_spec_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalOrbit

variable {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'}

theorem spMap_gal_comp (σ : Gal ρ) : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
  rw [← Spec.map_comp]; congr 1; ext r; exact σ.2 r

theorem spMap_gal_mul (σ τ : Gal ρ) :
    spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_gal_one : spMap (Gal.hom (1 : Gal ρ)) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

variable {X Z : Scheme.{0}} {f : X ⟶ Sp R} {p : Z ⟶ X} {s : Z ⟶ Sp R'}
  (hpb : IsPullback p s f (spMap ρ))

def act (σ : Gal ρ) : Z ⟶ Z :=
  hpb.lift p (s ≫ spMap (Gal.hom σ)) (by rw [Category.assoc, spMap_gal_comp, hpb.w])

@[reassoc] theorem act_p (σ : Gal ρ) : act hpb σ ≫ p = p := hpb.lift_fst _ _ _

@[reassoc] theorem galoisBaseChangeSchemeAction_comp_snd (σ : Gal ρ) : act hpb σ ≫ s = s ≫ spMap (Gal.hom σ) := hpb.lift_snd _ _ _

theorem act_one : act hpb 1 = 𝟙 Z :=
  hpb.hom_ext (by rw [act_p, Category.id_comp]) (by rw [galoisBaseChangeSchemeAction_comp_snd, spMap_gal_one, Category.comp_id, Category.id_comp])

theorem act_mul (σ τ : Gal ρ) : act hpb (σ * τ) = act hpb σ ≫ act hpb τ :=
  hpb.hom_ext (by rw [act_p, Category.assoc, act_p, act_p])
    (by rw [galoisBaseChangeSchemeAction_comp_snd, Category.assoc, galoisBaseChangeSchemeAction_comp_snd, galoisBaseChangeSchemeAction_comp_snd_assoc, spMap_gal_mul])

def actAut : Gal ρ →* Aut Z where
  toFun σ :=
    { hom := act hpb σ⁻¹
      inv := act hpb σ
      hom_inv_id := by rw [← act_mul, inv_mul_cancel, act_one]
      inv_hom_id := by rw [← act_mul, mul_inv_cancel, act_one] }
  map_one' := Iso.ext (by change act hpb 1⁻¹ = 𝟙 Z; rw [inv_one, act_one])
  map_mul' σ τ := Iso.ext (by change act hpb (σ * τ)⁻¹ = act hpb τ⁻¹ ≫ act hpb σ⁻¹; rw [mul_inv_rev, act_mul])

end GlobalTheory.Mum.GalOrbit

namespace GlobalTheory.Mum

theorem gal_transitive_on_fibres : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'],
    Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (Y : Over (Sp R)), Flat Y.hom →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ Y.left) (s : Z ⟶ Sp R'), IsPullback p s Y.hom (spMap (algebraMap R R')) →
    ∀ z z' : Z, p z = p z' → ∃ (σ : Gal (algebraMap R R')) (h : Z ⟶ Z),
      h ≫ p = p ∧ h ≫ s = s ≫ spMap (Gal.hom σ) ∧ h z = z' := by
  intro R R' _ _ _ hinj hG Y hfl Z p s hpb z z' hzz
  have : Finite (Gal (algebraMap R R')) := hG.1
  have : Flat Y.hom := hfl
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hinv : ∀ W : Y.left.Opens, IsAffineOpen W → ∀ u : Γ(Z, p ⁻¹ᵁ W),
      GlobalTheory.IsInvariantSection (GalOrbit.actAut hpb) _ u → u ∈ Set.range (p.app W) := by
    intro W hW u hu
    refine (InvFun.affine_inv (algebraMap R R') hinj hG hpb (GalOrbit.act hpb) (GalOrbit.act_p hpb)
      (GalOrbit.galoisBaseChangeSchemeAction_comp_snd hpb) hW).2 u fun σ hσ => ?_
    obtain ⟨h₁, h₂⟩ := hu σ⁻¹
    have key : ∀ (τ τ' : Gal (algebraMap R R')) (_ : τ = τ') (e : p ⁻¹ᵁ W ≤ GalOrbit.act hpb τ ⁻¹ᵁ (p ⁻¹ᵁ W))
        (e' : p ⁻¹ᵁ W ≤ GalOrbit.act hpb τ' ⁻¹ᵁ (p ⁻¹ᵁ W)),
        ((GalOrbit.act hpb τ).appLE _ _ e).hom u = ((GalOrbit.act hpb τ').appLE _ _ e').hom u := by
      rintro τ _ rfl _ _; rfl
    exact (key _ _ (inv_inv σ).symm hσ h₁).trans h₂
  obtain ⟨g, hg⟩ := (GlobalTheory.apply_eq_iff_exists_aut_of_invariant (GalOrbit.actAut hpb) p
    (fun g => GalOrbit.act_p hpb _) hinv z z').1 hzz
  exact ⟨g⁻¹, GalOrbit.act hpb g⁻¹, GalOrbit.act_p hpb _, GalOrbit.galoisBaseChangeSchemeAction_comp_snd hpb _, hg⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingPairSectionsNormBounds
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.GenLow

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_pos_bounds {Y : Type} [TopologicalSpace Y] [CompactSpace Y] (G : Y → ℝ) (hG : Continuous G)
    (hpos : ∀ y, 0 < G y) : ∃ m U : ℝ, 0 < m ∧ 0 < U ∧ ∀ y, m ≤ G y ∧ G y ≤ U := by
  rcases isEmpty_or_nonempty Y with h | h
  · exact ⟨1, 1, one_pos, one_pos, fun y => (h.false y).elim⟩
  · obtain ⟨a, -, ha⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hG.continuousOn
    obtain ⟨b, -, hb⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hG.continuousOn
    exact ⟨G a, G b, hpos a, hpos b, fun y => ⟨ha (Set.mem_univ y), hb (Set.mem_univ y)⟩⟩

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem continuous_nu (P : Pair p) (a b : ℤ) (M : HermLB p) (hM : P.Rep a b M) (σ : k →+* ℂ)
    (f : X.functionField) (hf : f ∈ P.H a b) : Continuous fun y : CxPts p σ => P.nu a b σ y f := by
  obtain ⟨e, -, hr, hn, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P a b M hM
  obtain ⟨u, rfl⟩ : f ∈ Set.range e := hr ▸ hf
  have h : (fun y : CxPts p σ => P.nu a b σ y (e u)) = fun y => Real.sqrt ((M.φ σ).nsq (secVal p σ u) y) := by
    funext y
    rw [← hn u σ y, Real.sqrt_sq (nu_nonneg P a b σ y _)]
  rw [h]
  exact ((M.cInf σ).continuous_nsq u).sqrt

theorem gen_low : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (c : ℕ), GenAt P c → ∃ (n : ℕ) (v : Fin n → X.functionField) (ρ : ℝ), 0 < ρ ∧
      (∀ i, v i ∈ P.Bl 0 c ρ⁻¹) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, ρ ≤ P.nu 0 c σ y (v i) := by
  intro k _ X _ p D hX P c ⟨n, v, hvH, hnz⟩
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P 0 c
  have hb : ∀ σ : k →+* ℂ, ∃ m U : ℝ, 0 < m ∧ 0 < U ∧ ∀ y : CxPts p σ,
      m ≤ ∑ i, P.nu 0 c σ y (v i) ∧ ∑ i, P.nu 0 c σ y (v i) ≤ U := by
    intro σ
    haveI : CompactSpace (CxPts p σ) := hX.compactSpace σ
    refine exists_pos_bounds _ (continuous_finsetSum _ fun i _ => continuous_nu P 0 c M hM σ (v i) (hvH i))
      fun y => ?_
    obtain ⟨i, hi⟩ := hnz σ y
    exact lt_of_lt_of_le ((nu_nonneg P 0 c σ y _).lt_of_ne' hi)
      (Finset.single_le_sum (fun j _ => nu_nonneg P 0 c σ y (v j)) (Finset.mem_univ i))
  choose m U hm hU hmU using hb
  have hlow : ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ σ, m₀ ≤ m σ := by
    rcases isEmpty_or_nonempty (k →+* ℂ) with h | h
    · exact ⟨1, one_pos, fun σ => (h.false σ).elim⟩
    · obtain ⟨σ, hσ⟩ := Finite.exists_min m
      exact ⟨m σ, hm σ, hσ⟩
  have hup : ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ σ, U σ ≤ U₀ := by
    rcases isEmpty_or_nonempty (k →+* ℂ) with h | h
    · exact ⟨1, one_pos, fun σ => (h.false σ).elim⟩
    · obtain ⟨σ, hσ⟩ := Finite.exists_max U
      exact ⟨U σ, hU σ, hσ⟩
  obtain ⟨m₀, hm₀, hm₀le⟩ := hlow
  obtain ⟨U₀, hU₀, hU₀le⟩ := hup
  have hn1 : (0 : ℝ) < ((max n 1 : ℕ) : ℝ) := by exact_mod_cast lt_max_of_lt_right one_pos
  refine ⟨n, v, min (m₀ / (max n 1 : ℕ)) U₀⁻¹, lt_min (div_pos hm₀ hn1) (inv_pos.2 hU₀), fun i => ⟨hvH i, fun σ y => ?_⟩,
    fun σ y => ?_⟩
  · calc P.nu 0 c σ y (v i) ≤ ∑ j, P.nu 0 c σ y (v j) :=
          Finset.single_le_sum (fun j _ => nu_nonneg P 0 c σ y (v j)) (Finset.mem_univ i)
      _ ≤ U σ := (hmU σ y).2
      _ ≤ U₀ := hU₀le σ
      _ = U₀⁻¹⁻¹ := (inv_inv U₀).symm
      _ ≤ (min (m₀ / (max n 1 : ℕ)) U₀⁻¹)⁻¹ :=
          inv_anti₀ (lt_min (div_pos hm₀ hn1) (inv_pos.2 hU₀)) (min_le_right _ _)
  · obtain ⟨i₀, -⟩ := hnz σ y
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact i₀.elim0
    have hmax : (max n 1 : ℕ) = n := max_eq_left hn
    have hsum : ∑ _j : Fin n, m₀ / (max n 1 : ℕ) ≤ ∑ j, P.nu 0 c σ y (v j) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmax, mul_div_cancel₀ _
        (by exact_mod_cast (show n ≠ 0 by omega))]
      exact (hm₀le σ).trans (hmU σ y).1
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le ⟨i₀, Finset.mem_univ _⟩ hsum
    exact ⟨i, (min_le_left _ _).trans hi⟩

end GlobalTheory.HSNef.GenLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_eighth_power_uniformised_is_polarised : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  first | exact @GlobalTheory.SharpGen.gen_eighthPower | exact GlobalTheory.SharpGen.gen_eighthPower | (intros; apply GlobalTheory.SharpGen.gen_eighthPower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePolarisationEqEighthPowerPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section

namespace GlobalTheory.Poinc.GenPull

theorem lbIso_gen_pull : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀), ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → LBIso A'.L (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' gm ψ hψ H
  have e0 : LBIso A'.L (A'.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id A'.isLB
  have hc : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id]; rfl
  have e1 : LBIso ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) (A'.L.pull (𝟙 _)) := by
    have := GlobalTheory.SiegelPullComp.iso_pull_pull A'.isLB U'.gen.hom.left U'.gen.inv.left
    rwa [hc] at this
  have e2 := GlobalTheory.SiegelPullComp.iso_pull U'.gen.inv.left U'.ext
  have e3 := GlobalTheory.SiegelPullComp.iso_pull_pull U'.LG.isLB (pullback.fst G'.hom (jK R)) U'.gen.inv.left
  have e4 := GlobalTheory.SiegelPullComp.iso_pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) H
  have e5 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB gm (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R))
  have hq : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm = ψ ≫ FinalForm.φ := by
    rw [Category.assoc, hψ]
  rw [hq] at e5
  have e6 := GlobalTheory.SiegelPullComp.iso_pull_pull FinalForm.L.isLB FinalForm.φ ψ
  have e7 := GlobalTheory.SiegelPullComp.iso_pull ψ (⟨FinalForm.w, FinalForm.w_gen⟩ : LBIso _ _)
  have e8 := GlobalTheory.SiegelPullComp.iso_pull_pull ρ.P.isLB (pullback.fst ρ.P.A.hom FinalForm.u₀) ψ
  have hA := A'.isLB
  have hG := U'.LG.isLB
  have hZ := FinalForm.L.isLB
  have hP := ρ.P.isLB
  refine LBIso.trans hA (pull_isLB (pull_isLB hA _) _) (pull_isLB hP _) (LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _) e0 e1.symm) ?_
  refine LBIso.trans (pull_isLB (pull_isLB hA _) _) (pull_isLB (pull_isLB hG _) _) (pull_isLB hP _) e2 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hG _) _) (pull_isLB hG _) (pull_isLB hP _) e3 ?_
  refine LBIso.trans (pull_isLB hG _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e4 ?_
  refine LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) (pull_isLB hP _) e5 ?_
  refine LBIso.trans (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) (pull_isLB hP _) e6.symm ?_
  exact LBIso.trans (pull_isLB (pull_isLB hZ _) _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e7 e8

end GlobalTheory.Poinc.GenPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreUniformisedModelPointGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
noncomputable section
namespace GlobalTheory.GenPb

theorem genfib_grpPullback : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ ψ : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, ψ ≫ FinalForm.φ = U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm ∧ ψ ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ ξ₀ ∧ IsGrpPullback A'.A ρ.P.A (ξ₀ ≫ FinalForm.u₀) (ψ ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G' _ _ D' A' U' ξ gm hgm ξ₀ hξ
  have := U'.gen_hom
  have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
  have gpA : IsGrpPullback A'.A G' (jK R) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) :=
    ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK R))).congr
      (Category.id_comp _) rfl
  have h2 : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ U₀.ι) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK R)) ≫ gm) :=
    (gpA.comp hgm).congr hξ.symm rfl
  have hw : (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) ≫ FinalForm.G.hom = (A'.A.hom ≫ ξ₀) ≫ U₀.ι := by
    have := h2.1.w
    simpa [Category.assoc] using this
  refine ⟨FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw,
    FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _, ?_⟩
  have h3 : IsGrpPullback A'.A ((Over.pullback FinalForm.u₀).obj ρ.P.A) ξ₀
      (FinalForm.cart.1.lift (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) (A'.A.hom ≫ ξ₀) hw) :=
    IsGrpPullback.cancel FinalForm.cart (h2.congr rfl (by rw [FinalForm.cart.1.lift_fst, Category.assoc]))
      (FinalForm.cart.1.lift_snd _ _ _)
  exact h3.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)

end GlobalTheory.GenPb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericOverPower
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen

theorem w_pow_succ_sub_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    (α β : AlgebraicClosure F) {E : ℝ} (hE : 0 ≤ E) (hα : e.w α * E ≤ 1) (hβ : e.w β * E ≤ 1) (k : ℕ) :
    e.w (α ^ (k + 1) - β ^ (k + 1)) * E ^ (k + 1) ≤ e.w (α - β) * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : α ^ (k + 1 + 1) - β ^ (k + 1 + 1) = α ^ (k + 1) * (α - β) + (α ^ (k + 1) - β ^ (k + 1)) * β := by ring
    rw [h]
    have hmax := TrueGeo.Ext.w_add_le_max F v e (α ^ (k + 1) * (α - β)) ((α ^ (k + 1) - β ^ (k + 1)) * β)
    have hEk : 0 ≤ E ^ (k + 1 + 1) := pow_nonneg hE _
    refine (mul_le_mul_of_nonneg_right hmax hEk).trans ?_
    rw [max_mul_of_nonneg _ _ hEk]
    refine max_le ?_ ?_
    · rw [map_mul, map_pow]
      have e1 : e.w α ^ (k + 1) * e.w (α - β) * E ^ (k + 1 + 1) = (e.w α * E) ^ (k + 1) * (e.w (α - β) * E) := by ring
      rw [e1]
      exact mul_le_of_le_one_left (mul_nonneg (e.w.nonneg _) hE) (pow_le_one₀ (mul_nonneg (e.w.nonneg _) hE) hα)
    · rw [map_mul]
      have e1 : e.w (α ^ (k + 1) - β ^ (k + 1)) * e.w β * E ^ (k + 1 + 1) =
          (e.w (α ^ (k + 1) - β ^ (k + 1)) * E ^ (k + 1)) * (e.w β * E) := by ring
      rw [e1]
      exact (mul_le_of_le_one_right (mul_nonneg (e.w.nonneg _) (pow_nonneg hE _)) hβ).trans ih

theorem w_pow_sub_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    (α β : AlgebraicClosure F) {E : ℝ} (hE : 0 ≤ E) (hα : e.w α * E ≤ 1) (hβ : e.w β * E ≤ 1) {m : ℕ} (hm : 0 < m) :
    e.w (α ^ m - β ^ m) * E ^ m ≤ e.w (α - β) * E := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact w_pow_succ_sub_le e α β hE hα hβ k

theorem unitAt_zpow' {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) (a : ℤ) :
    UnitAt x (f ^ a) := by
  obtain ⟨_, ⟨u, rfl⟩, rfl⟩ := h
  refine ⟨((u ^ a : _ˣ) : X.presheaf.stalk x), Units.isUnit _, ?_⟩
  exact (congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u a)).trans
    (Units.val_zpow_eq_zpow_val _ _)

theorem regAt_sub' {X : Scheme.{0}} [IsIntegral X] {x : X} {f g : X.functionField} (hf : RegAt x f) (hg : RegAt x g) :
    RegAt x (f - g) :=
  have ⟨a, ha⟩ := hf; have ⟨b, hb⟩ := hg; ⟨a - b, by rw [map_sub, ha, hb]⟩

theorem valAt_sub' {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] {y : Sp K ⟶ X} {f g : X.functionField}
    (hf : RegAt (below y) f) (hg : RegAt (below y) g) : TrueGeo.valAt y (f - g) = TrueGeo.valAt y f - TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_sub, TrueGeo.Res.valAt_algebraMap, TrueGeo.Res.valAt_algebraMap, TrueGeo.Res.valAt_algebraMap, map_sub]

theorem genOver_pow_div : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (f : Y.X → Y.Fn)
    (ψ φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l m : ℕ) (a : ℤ), l ≠ 0 → 0 < m →
    (∀ v e y, (l : 𝓞 F) ∈ v.asIdeal → φ v e y = m * ψ v e y + a * Real.log (e.w (l : AlgebraicClosure F))) →
    GenOver V f ψ l → GenOver V (fun y => f y ^ m) φ l := by
  intro F _ _ Y V f ψ φ l m a hl hm hφ ⟨n, U, s, hU, hreg, hnorm⟩
  have hlF : (l : F) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hl1 : ∀ z : V.G, UnitAt z (l : V.G.functionField) := fun z => by
    have := TrueGeo.IndScale.unitAt_constFn (V.π ≫ Y.str) z hlF
    rwa [map_natCast] at this
  have hlu : ∀ z : V.G, UnitAt z ((l : V.G.functionField) ^ (-a)) := fun z => unitAt_zpow' (hl1 z) (-a)
  have key : ∀ (p : Y.X) (x : V.X) (J : Fin n), (s x J ^ m * (l : V.G.functionField) ^ (-a)) / V.φ (f p ^ m) =
      (s x J / V.φ (f p)) ^ m * (l : V.G.functionField) ^ (-a) := by
    intro p x J
    rw [map_pow, div_pow, div_mul_eq_mul_div]
  have keyd : ∀ (p : Y.X) (x x' : V.X) (J : Fin n),
      (s x J ^ m * (l : V.G.functionField) ^ (-a) - s x' J ^ m * (l : V.G.functionField) ^ (-a)) / V.φ (f p ^ m) =
      ((s x J / V.φ (f p)) ^ m - (s x' J / V.φ (f p)) ^ m) * (l : V.G.functionField) ^ (-a) := by
    intro p x x' J
    rw [map_pow, div_pow, div_pow, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, sub_div]
  refine ⟨n, U, fun x J => s x J ^ m * (l : V.G.functionField) ^ (-a), hU, fun x J z hz => ?_, ?_⟩
  · beta_reduce
    rw [key]
    exact (TrueGeo.Res.regAt_pow (hreg x J z hz) m).mul (hlu z).regAt
  · intro v e y z yt hlv hzy hyt x hx
    beta_reduce
    have hπ : V.π (below z) = below y.1 := by rw [← hzy]; rfl
    have hmem : ∀ x', ⊤ ≤ yt ⁻¹ᵁ U x' → V.j (below z) ∈ U x' := fun x' h => by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x' := by rw [← hyt]; exact h (Set.mem_univ _)
      exact h1
    have hα : ∀ x', ⊤ ≤ yt ⁻¹ᵁ U x' → ∀ J, RegAt (below z) (s x' J / V.φ (f (below y.1))) := fun x' h J => by
      have := hreg x' J (below z) (hmem x' h)
      rwa [hπ] at this
    have hl0 : (l : AlgebraicClosure F) ≠ 0 := by
      have := (algebraMap F (AlgebraicClosure F)).injective.ne hlF
      rwa [map_natCast, map_zero] at this
    have hwl : 0 < e.w (l : AlgebraicClosure F) := e.w.pos hl0
    have hvl : TrueGeo.valAt z ((l : V.G.functionField) ^ (-a)) = (l : AlgebraicClosure F) ^ (-a) := by
      rw [(TrueGeo.Base.valAt_zpow z (hl1 (below z))).2 (-a)]
      congr 1
      rw [← map_natCast (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField), TrueGeo.Res.valAt_algebraMap,
        map_natCast]
    have hE : Real.exp (φ v e y) = Real.exp (ψ v e y) ^ m * e.w (l : AlgebraicClosure F) ^ a := by
      rw [hφ v e y hlv, Real.exp_add, Real.exp_nat_mul, mul_comm (a : ℝ), ← Real.rpow_def_of_pos hwl, Real.rpow_intCast]
    have hscale : ∀ β, RegAt (below z) β → e.w (TrueGeo.valAt z (β * (l : V.G.functionField) ^ (-a))) *
        Real.exp (φ v e y) = e.w (TrueGeo.valAt z β) * Real.exp (ψ v e y) ^ m := by
      intro β hβ
      rw [TrueGeo.Res.valAt_mul hβ (hlu _).regAt, hvl, map_mul, map_zpow₀, hE]
      have h1 : e.w (l : AlgebraicClosure F) ^ (-a) * e.w (l : AlgebraicClosure F) ^ a = 1 := by
        rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hwl.ne')]
      linear_combination (e.w (TrueGeo.valAt z β) * Real.exp (ψ v e y) ^ m) * h1
    obtain ⟨h1, ⟨J₀, h2⟩, h3⟩ := hnorm v e y z yt hlv hzy hyt x hx
    have hE0 : 0 ≤ Real.exp (ψ v e y) := (Real.exp_pos _).le
    refine ⟨fun J => ?_, ⟨J₀, ?_⟩, fun x' hx' J => ?_⟩
    · rw [key, hscale _ (TrueGeo.Res.regAt_pow (hα x hx J) m), TrueGeo.Res.valAt_pow (hα x hx J), map_pow, ← mul_pow]
      exact pow_le_one₀ (mul_nonneg (e.w.nonneg _) hE0) (h1 J)
    · rw [key, hscale _ (TrueGeo.Res.regAt_pow (hα x hx J₀) m), TrueGeo.Res.valAt_pow (hα x hx J₀), map_pow,
        ← mul_pow, h2, one_pow]
    · have h1' := (hnorm v e y z yt hlv hzy hyt x' hx').1 J
      have h3' := h3 x' hx' J
      rw [sub_div, valAt_sub' (hα x hx J) (hα x' hx' J)] at h3'
      rw [keyd, hscale _ (regAt_sub' (TrueGeo.Res.regAt_pow (hα x hx J) m) (TrueGeo.Res.regAt_pow (hα x' hx' J) m)),
        valAt_sub' (TrueGeo.Res.regAt_pow (hα x hx J) m) (TrueGeo.Res.regAt_pow (hα x' hx' J) m),
        TrueGeo.Res.valAt_pow (hα x hx J), TrueGeo.Res.valAt_pow (hα x' hx' J)]
      exact (w_pow_sub_le e _ _ hE0 (h1 J) h1' hm).trans_lt h3'

end GlobalTheory.HtGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.flat_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) : Flat M.gp := by
  haveI := M.integral
  haveI := M.dominant
  refine Flat.of_stalkMap _ fun x => ?_
  have hx : M.gp.base x = genericPoint M.S := by
    have hd : DenseRange M.gp.base := M.gp.denseRange
    have hr : Set.range M.gp.base = {M.gp.base x} := by
      ext y; constructor
      · rintro ⟨z, rfl⟩; rw [Subsingleton.elim z x]; rfl
      · rintro rfl; exact ⟨x, rfl⟩
    have hg : IsGenericPoint (M.gp.base x) ⊤ := by
      rw [IsGenericPoint, ← hr]
      simpa [Set.top_eq_univ] using hd.closure_range
    exact hg.eq (genericPoint_spec M.S)
  have hF : IsField (M.S.presheaf.stalk (M.gp.base x)) := by
    rw [hx]; exact Field.toIsField _
  letI : Field (M.S.presheaf.stalk (M.gp.base x)) := hF.toField
  unfold RingHom.Flat
  exact inferInstance

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_of_isPullback_surjective_lft : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  first | exact @GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective | exact GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective | (intros; apply GlobalTheory.Mum.geometricallyConnected_of_isPullback_of_surjective <;> assumption)
end

