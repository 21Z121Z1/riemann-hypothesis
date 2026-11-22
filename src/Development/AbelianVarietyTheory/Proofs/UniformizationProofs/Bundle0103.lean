import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.EvenTriv

theorem exists_even_cubTriv_specialFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (P : CP G) (w : G ⟶ G), IsMonHom w → LBIso P.L.L (cubeLB G ![𝟙 G, w] P.L.L) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ (thickObj V (maximalIdeal V) 0 G) X) (P₀ : CP (thickObj V (maximalIdeal V) 0 G)), IsLevelCP (maximalIdeal V) 0 P₀ P → ∃ σ : CubTriv P₀.c Q₀.i, σ.Even := by
  intro _ V _ _ _ _ A G _ _ hG gen _ P w _ hw X _ _ _ Q₀ P₀ ⟨v, hv⟩
  have hp : IsProper (pullback.snd G.hom (jK V)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK V) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper gen.hom.left A.A.hom inferInstance A.isAb.proper
  have hm : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V ⧸ maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  have hS := IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG
  have := hS.smooth
  have := hS.geomConnected
  have := Q₀.i_hom
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V ⧸ maximalIdeal V ^ (0 + 1)) X (thickObj V (maximalIdeal V) 0 G) P₀.L P₀.c Q₀.i
    Q₀.i_hom
  exact exists_even_of_surjective (surjective_cube_of_generic G hG hp) P w hw P₀
    (IsPullback.of_hasPullback G.hom (thick V (maximalIdeal V) 0)) hv Q₀.i s

end GlobalTheory.EvenTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpFOfFam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpOnto

theorem exists_sec_comb {X : Scheme.{0}} {L : LB X} {n : ℕ} (r : Fin n → Γ(X, ⊤)) (b : Fin n → LB.Sec L) :
    ∃ t : LB.Sec L, ∀ j, t.f j = ∑ i, resTop _ (r i) * (b i).f j := by
  induction n with
  | zero => exact ⟨DVR.SecOps.secZero, fun j => by simp [DVR.SecOps.secZero]⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (fun i => r i.succ) (fun i => b i.succ)
    refine ⟨DVR.SecOps.secAdd (DVR.SecOps.secScale (r 0) (b 0)) t, fun j => ?_⟩
    rw [Fin.sum_univ_succ, ← ht j]
    rfl

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {K : Type} (S : Finset K) (s : K → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DVR.add_f, ih]

theorem exists_expF_of_fam : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → U.FE F k → ∀ s : Fam D F k, ∃ t, U.ExpF F k t s.s := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB F _ _ k hk hFE s
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow_field hL2.secTwist V A F k hk
  choose e he using fun i => GlobalTheory.T.exists_fourierJacobi_expansion_over_field hL hL2 V hV D A G U F k hk (b i)
  let f : Fin (k ^ A.g) → Fam D F k := fun i => ⟨e i, hFE _ _ (he i)⟩
  have comb : ∀ c : Fin (k ^ A.g) → F, ∃ t, (∀ j, t.f j = ∑ i,
      liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j) ∧
      U.ExpF F k t (∑ i, c i • f i).s := fun c => by
    obtain ⟨t, ht⟩ := exists_sec_comb (fun i => (fst (TFK (R := V) F) A.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b
    refine ⟨t, ht, ExpLinC.expF_lincomb V hV D A G U F k _ c b e t _ he ht fun α j => ?_⟩
    exact fam_sum_f _ _ α j
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨t, ht, hE⟩ := comb c
    obtain ⟨t', ht', hE'⟩ := comb 0
    have h0 : (∑ i, (0 : Fin (k ^ A.g) → F) i • f i) = ∑ i, c i • f i := by
      rw [hc]; simp
    have htt : t = t' := (GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k t t' _ _ hE hE').2 (by rw [h0])
    subst htt
    exact congrFun ((hb t).unique ht ht')
  obtain ⟨hfin, hdim⟩ := finrank_fam_of_laws hL hL2 V D hB F k hk
  have hg : A.g = D.P.g + D.rank := PreU.dim_eq V hV D A G U
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [hdim, Fintype.card_fin, hg])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (hsp ▸ Submodule.mem_top (x := s))
  obtain ⟨t, -, hE⟩ := comb c
  exact ⟨t, hc ▸ hE⟩

end GlobalTheory.UU.ExpOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFunctionalEquationSectionNonzeroClassStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionalEquation_section_nonzero_class : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ k : ℕ, 1 ≤ k → U.FE (Kbar V) 1 → U.FE (Kbar V) k → (∃ β, U.Supp (Kbar V) 1 β) → (∃ β, U.Supp (Kbar V) k β) → ∀ α, ∃ t s, U.ExpF (Kbar V) (k + 1) t s ∧ DegPre.FamFE D (Kbar V) (k + 1) s ∧ ∃ j, (s α).f j ≠ 0 := by
  first | exact @GlobalTheory.UU.FESection.main | exact GlobalTheory.UU.FESection.main | (intros; apply GlobalTheory.UU.FESection.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIntegral

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 := by
  refine (congrArg (gs r z _) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_sec_ne_zero (h1 : Laws) (h2 : Laws2) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type)
    [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) :
    ∃ v : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p), v ≠ 0 := by
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep h1 h2 S P F p 1 (by simp)
  have : Nontrivial Γ((Over.mk p).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have : Nontrivial (SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk p)) :=
    Module.nontrivial_of_finrank_pos (R := Γ((Over.mk p).left, ⊤)) (by rw [hr]; simp)
  exact exists_ne 0

theorem exists_theta : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U
  obtain ⟨v, hv⟩ := exists_sec_ne_zero h1 h2 _ A (Kbar V) (jFK (R := V) (Kbar V))
  obtain ⟨s, n, c, σ, f, hE, hA, -⟩ := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U (Kbar V) 1 le_rfl (SecM.toSec A.A v)
  by_contra hn
  have hz : ∀ i j, (σ i).f j = 0 := fun i j => by
    by_contra h
    exact hn ⟨σ i, f i, hE i, j, h⟩
  refine hv (Subtype.ext (funext fun j => ?_))
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := V) (Kbar V)) A.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let y := (snd (TFK (R := V) (Kbar V)) A.A).left ≫ U.gen.inv.left
  let T : Over (Spec (CommRingCat.of V)) := Over.mk ((y ≫ pullback.fst G.hom (jK V)) ≫ G.hom)
  let x : T ⟶ G := Over.homMk (y ≫ pullback.fst G.hom (jK V)) rfl
  have e := hA _ (𝟙 _) y (lift (toUnit T) x).left
    (by rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
    (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG
  rw [Finset.sum_eq_zero fun i _ => by rw [sval_eq_zero (σ i) (hz i), mul_zero], ← Units.val_pow_eq_pow_val,
    Units.mul_right_eq_zero] at e
  exact e.trans (sval_eq_zero _ (fun _ => rfl) _ _ _).symm

end GlobalTheory.ThetaIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamily
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpLinMap

theorem exists_linear_of_rel {F M X : Type} [Field F] [AddCommGroup M] [Module F M] {N : X → Type}
    [∀ α, AddCommGroup (N α)] [∀ α, Module F (N α)] (E : M → (∀ α, N α) → Prop)
    (tot : ∀ t, ∃ s, E t s) (uq : ∀ t t' s s', E t s → E t' s' → (t = t' ↔ s = s'))
    (lin : ∀ (c : F) t t' s s', E t s → E t' s' → E (c • t + t') (fun α => c • s α + s' α)) :
    ∃ ex : ∀ α, M →ₗ[F] N α, (∀ t, E t (fun α => ex α t)) ∧ (∀ t s, E t s → ∀ α, s α = ex α t) ∧
      (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, ((∃ t s, E t s ∧ s α ≠ 0) ↔ ex α ≠ 0) := by
  choose e he using tot
  have hl : ∀ (c : F) t t' α, e (c • t + t') α = c • e t α + e t' α := fun c t t' α =>
    congrFun ((uq _ _ _ _ (he _) (lin c t t' _ _ (he t) (he t'))).1 rfl) α
  have h0 : ∀ α, e 0 α = 0 := fun α => by
    have h := hl 1 0 0 α
    simpa using h
  have hu : ∀ t s, E t s → ∀ α, s α = e t α := fun t s h α => congrFun ((uq _ _ _ _ h (he t)).1 rfl) α
  refine ⟨fun α => ⟨⟨fun t => e t α, fun t t' => ?_⟩, fun c t => ?_⟩, he, hu, fun t h => ?_, fun α => ⟨?_, fun h => ?_⟩⟩
  · simpa using hl 1 t t' α
  · simpa [h0] using hl c t 0 α
  · exact (uq _ _ _ _ (he t) (he 0)).2 (funext fun α => (h α).trans (h0 α).symm)
  · rintro ⟨t, s, h, hs⟩ hz
    exact hs ((hu t s h α).trans (LinearMap.congr_fun hz t))
  · by_contra hn
    refine h (LinearMap.ext fun t => ?_)
    by_contra ht
    exact hn ⟨t, e t, he t, ht⟩

theorem exists_expansion_linear : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  intro h1 h2 V _ _ _ hV D A G _ _ U F _ _ k hk
  obtain ⟨ex, a, b, c, d⟩ := exists_linear_of_rel (F := F) (M := EA A (jFK (R := V) F) k) (N := fun α => WB D F k α)
    (fun t s => U.ExpF F k t.sec (fun α => (s α).sec))
    (fun t => GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D A G U F k hk t.sec)
    (fun t t' s s' h h' => GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k t.sec t'.sec _ _ h h')
    (fun c t t' s s' h h' => ExpLin.expF_linear V hV D A G U F k t.sec t'.sec _ _ _ _ c h h'
      (fun _ => rfl) (fun _ _ => rfl))
  refine ⟨ex, a, fun t s h α => b (SecMod.mk _ t) (fun α => SecMod.mk _ (s α)) h α, c, fun α => Iff.trans ?_ (d α)⟩
  constructor
  · rintro ⟨t, s, h, j, hj⟩
    exact ⟨SecMod.mk _ t, fun α => SecMod.mk _ (s α), h, fun hz => hj ((SecMod.eq_zero_iff_coord _).1 hz j)⟩
  · rintro ⟨t, s, h, hs⟩
    exact ⟨t.sec, fun α => (s α).sec, h, not_forall.1 fun hz => hs ((SecMod.eq_zero_iff_coord _).2 hz)⟩

end GlobalTheory.UU.ExpLinMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecExpandsAtOfIntegralFamily
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_expandsAt_of_integral_family : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom], (∀ F : Fam D.toPre (FractionRing R) k, ∃ s : U.SecK k, U.Expands k s F) → ∀ (F : Fam D.toPre (FractionRing R) k) (f : ∀ α, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α) (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), ∀ e, U.ExpandsAt e k σ f := by
  intro R _ _ I hR D A G _ _ _ U k _ hall F f hf
  obtain ⟨s, r, hr, σ₀, f₀, -, hf₀, hE⟩ := hall F
  have hw : (D.toPre.prB (FractionRing R)).left ≫ D.toPre.P.A.hom = (D.toPre.BF (FractionRing R)).hom := Over.w _
  have hm : ∀ α, DVR.SecIsMul D.toPre.P.A.hom r (f₀ α) (f α) := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom
      (fun W => GlobalTheory.IntegralExpansion.prB_app_injective D.toPre W) (hf α) (by rw [hw]; exact hf₀ α)
  have hm' : ∀ α, ∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j := fun α j => hm α j
  obtain ⟨σ, hσ⟩ := GlobalTheory.sec_div_of_expandsAt R I hR D A G U k r hr σ₀ f₀ f hm' hE
  exact ⟨σ, GlobalTheory.T.expandsAt_cancel_nonzero_scalar R I hR D A G U k r hr σ₀ σ f₀ f hm' hσ hE⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionPrimitiveTwistTorusExtension
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtSec

theorem stalkMap_injective {X Z : Scheme.{0}} (r : Z ⟶ X) [Flat r] (z : Z) :
    Function.Injective (r.stalkMap z).hom :=
  (injective_iff_map_eq_zero _).2 fun b hb =>
    zero_dvd_iff.1 (dvd_descend r z (a := 0) (b := b) (by rw [hb, map_zero]))

theorem exists_gs_ne_zero {X : Scheme.{0}} {V : X.Opens} {a : Γ(X, V)} (ha : a ≠ 0) :
    ∃ x ∈ V, gs (𝟙 X) x V a ≠ 0 := by
  by_contra h
  refine ha (fn_ext fun x hx => ?_)
  rw [LBGerm.gs_zero _ x V hx]
  exact by_contra fun k => h ⟨x, hx, k⟩

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem isWt_sub {i : splitTorus S X ⟶ G} {V : G.left.Opens} {u v : Γ(G.left, V)} {χ : X} (hu : IsWt i V u χ)
    (hv : IsWt i V v χ) : IsWt i V (u - v) χ :=
  fun Z t g h₁ h₂ => by rw [map_sub, map_sub, hu Z t g h₁ h₂, hv Z t g h₁ h₂, mul_sub]

variable (Q : TQ G X)

theorem isWt_app (V : Q.B.left.Opens) (c : Γ(Q.B.left, V)) : IsWt Q.i _ ((Q.q.left.app V).hom c) 0 := by
  intro Z t g k₁ k₂
  have e : ∀ (r : Z.left ⟶ G.left) (k : ⊤ ≤ r ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V)),
      (r.appLE _ ⊤ k).hom ((Q.q.left.app V).hom c) = ((r ≫ Q.q.left).appLE V ⊤ k).hom c := fun r k =>
    (congrArg (fun q => q.hom c) (Scheme.Hom.comp_appLE r Q.q.left V ⊤ k)).symm
  have e' : ∀ (r r' : Z.left ⟶ Q.B.left) (_ : r = r') (k : ⊤ ≤ r ⁻¹ᵁ V) (k' : ⊤ ≤ r' ⁻¹ᵁ V),
      (r.appLE V ⊤ k).hom c = (r'.appLE V ⊤ k').hom c := by
    rintro r _ rfl k k'; rfl
  rw [e, e, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
  have k : ((t ≫ Q.i) * g).left ≫ Q.q.left = g.left ≫ Q.q.left := by
    rw [← Over.comp_left, ← Over.comp_left, WtBundle.act_comp]
  exact e' _ _ k _ _

theorem exists_app_of_isWt (V : Q.B.left.Opens) (a : Γ(G.left, Q.q.left ⁻¹ᵁ V)) (h : IsWt Q.i _ a 0) :
    ∃ c, (Q.q.left.app V).hom c = a := by
  have := Q.q_affine
  refine (invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V).2.2 a fun Z t g k₁ k₂ => ?_
  rw [h Z t g k₁ k₂, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]

theorem graded (V : Q.B.left.Opens) (hV : IsAffineOpen V) :
    (∀ u : Γ(G.left, Q.q.left ⁻¹ᵁ V), ∃ a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V),
      (∀ χ, IsWt Q.i _ (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
    ∀ a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V), (∀ χ, IsWt Q.i _ (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0 := by
  have := Q.q_affine
  refine GlobalTheory.functions_graded_by_weights S G X Q.i Q.i_hom _ (hV.preimage _) ?_
  have e := congrArg (fun q => q.left) (WtBundle.act_comp Q (fst (splitTorus _ X) G) (snd _ G))
  simp only [Over.comp_left] at e
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, e]

theorem comp_compat {V V' U : Q.B.left.Opens} (g : Γ(Q.B.left, U)) (hU : V ⊓ V' ≤ U)
    (a : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V)) (a' : X →₀ Γ(G.left, Q.q.left ⁻¹ᵁ V'))
    (ha : ∀ χ, IsWt Q.i _ (a χ) χ) (ha' : ∀ χ, IsWt Q.i _ (a' χ) χ)
    (h : ∀ x, Q.q.left x ∈ V → Q.q.left x ∈ V' → gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V) (a.sum fun _ x => x) =
      gs Q.q.left x U g * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V') (a'.sum fun _ x => x))
    (χ : X) (x : G.left) (hx : Q.q.left x ∈ V) (hx' : Q.q.left x ∈ V') :
    gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V) (a χ) = gs Q.q.left x U g * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V') (a' χ) := by
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (show Q.q.left x ∈ V ⊓ V' from ⟨hx, hx'⟩)
  have hle : W ≤ V ⊓ V' := hle
  have l₁ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ V := fun _ k => (hle k).1
  have l₂ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ V' := fun _ k => (hle k).2
  have l₃ : Q.q.left ⁻¹ᵁ W ≤ Q.q.left ⁻¹ᵁ U := fun _ k => hU (hle k)
  let g' : Γ(G.left, Q.q.left ⁻¹ᵁ W) := (G.left.presheaf.map (homOfLE l₃).op).hom ((Q.q.left.app U).hom g)
  let r₁ : Γ(G.left, Q.q.left ⁻¹ᵁ V) →+ Γ(G.left, Q.q.left ⁻¹ᵁ W) :=
    (G.left.presheaf.map (homOfLE l₁).op).hom.toAddMonoidHom
  let r₂ : Γ(G.left, Q.q.left ⁻¹ᵁ V') →+ Γ(G.left, Q.q.left ⁻¹ᵁ W) :=
    (AddMonoidHom.mulLeft g').comp (G.left.presheaf.map (homOfLE l₂).op).hom.toAddMonoidHom
  have v : ∀ y, Q.q.left y ∈ W → ∀ b b', gs (𝟙 _) y (Q.q.left ⁻¹ᵁ W) (r₁ b - r₂ b') =
      gs (𝟙 _) y (Q.q.left ⁻¹ᵁ V) b - gs Q.q.left y U g * gs (𝟙 _) y (Q.q.left ⁻¹ᵁ V') b' := fun y hy b b' => by
    refine (LBGerm.gs_sub (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy _ _).trans (congrArg₂ (· - ·) (gs_res (𝟙 _) y l₁ hy _)
      ((gs_mul (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy g' _).trans (congrArg₂ (· * ·) ((gs_res (𝟙 _) y l₃ hy _).trans ?_)
        (gs_res (𝟙 _) y l₂ hy _))))
    rw [gs_pull (𝟙 _) Q.q.left y U (l₃ hy), Category.id_comp]
  have s : ∀ {A B : Type} [AddCommGroup A] [AddCommGroup B] (r : A →+ B) (b : X →₀ A),
      ((b.mapRange r (map_zero r)).sum fun _ x => x) = r (b.sum fun _ x => x) := fun r b => by
    rw [Finsupp.sum_mapRange_index (fun _ => rfl), map_finsuppSum]
  have z := (graded Q W hW).2 (a.mapRange r₁ (map_zero r₁) - a'.mapRange r₂ (map_zero r₂))
    (fun ψ => isWt_sub ((ha ψ).res l₁) (by
      have := ((isWt_app Q U g).res l₃).mul ((ha' ψ).res l₂)
      rwa [zero_add] at this)) (by
      rw [Finsupp.sum_sub_index (fun _ _ _ => rfl), s, s]
      refine fn_ext fun y hy => ?_
      rw [v y hy, h y (l₁ hy) (l₂ hy), sub_self, LBGerm.gs_zero (𝟙 _) y (Q.q.left ⁻¹ᵁ W) hy])
  have z' : r₁ (a χ) - r₂ (a' χ) = 0 := DFunLike.congr_fun z χ
  rw [← sub_eq_zero, ← v x hxW, z', LBGerm.gs_zero (𝟙 _) x (Q.q.left ⁻¹ᵁ W) hxW]

theorem exists_component (M : LB Q.B.left) (hM : M.IsLB) (s : LB.Sec (M.pull Q.q.left)) (hs : ∃ j, s.f j ≠ 0) :
    ∃ (χ : X) (α : Type) (V : α → Q.B.left.Opens) (i : α → M.ι) (f : ∀ p, Γ(G.left, Q.q.left ⁻¹ᵁ V p)),
      (∀ p, V p ≤ M.U (i p)) ∧ (∀ y, ∃ p, y ∈ V p) ∧ (∀ p, IsWt Q.i _ (f p) χ) ∧ (∃ p, f p ≠ 0) ∧
      ∀ p p' x, Q.q.left x ∈ V p → Q.q.left x ∈ V p' → gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p) (f p) =
        (gm Q.q.left x (M.U (i p) ⊓ M.U (i p')) (M.g (i p) (i p'))).val * gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p') (f p') := by
  let α := {p : Q.B.left.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2}
  have le : ∀ p : α, Q.q.left ⁻¹ᵁ p.1.1 ≤ (M.pull Q.q.left).U fun _ => p.1.2 := fun p _ k => mem_pull.2 (p.2.2 k)
  choose a ha hsum using fun p : α => (graded Q p.1.1 p.2.1).1
    ((G.left.presheaf.map (homOfLE (le p)).op).hom (s.f fun _ => p.1.2))
  have cov : ∀ y j, y ∈ M.U j → ∃ p : α, y ∈ p.1.1 ∧ p.1.2 = j := fun y j hj => by
    obtain ⟨W, hW, hy, hle⟩ := exists_isAffineOpen_mem_and_subset hj
    exact ⟨⟨(W, j), hW, hle⟩, hy, rfl⟩
  obtain ⟨J, hJ⟩ := hs
  obtain ⟨x, hx, hx0⟩ := exists_gs_ne_zero hJ
  obtain ⟨p₀, hp, e⟩ := cov _ _ (mem_pull.1 hx)
  obtain rfl : (fun _ => p₀.1.2) = J := funext fun _ => e
  have n : a p₀ ≠ 0 := fun k => hx0 (by
    rw [← gs_res (𝟙 _) x (le p₀) hp, hsum, k, Finsupp.sum_zero_index,
      LBGerm.gs_zero (𝟙 _) x (Q.q.left ⁻¹ᵁ p₀.1.1) hp])
  obtain ⟨χ, hχ⟩ := Finsupp.ne_iff.1 n
  refine ⟨χ, α, fun p => p.1.1, fun p => p.1.2, fun p => a p χ, fun p => p.2.2, fun y => ?_, fun p => ha p χ,
    ⟨p₀, hχ⟩, fun p p' x hx hx' => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart hM y
    exact (cov y j hj).imp fun _ k => k.1
  · rw [← gs_unit Q.q.left x (M.U p.1.2 ⊓ M.U p'.1.2) ⟨p.2.2 hx, p'.2.2 hx'⟩]
    refine comp_compat Q _ (inf_le_inf p.2.2 p'.2.2) _ _ (ha p) (ha p') (fun y hy hy' => ?_) χ x hx hx'
    rw [← hsum, ← hsum, gs_res (𝟙 _) y (le p) hy, gs_res (𝟙 _) y (le p') hy',
      gs_unit Q.q.left y (M.U p.1.2 ⊓ M.U p'.1.2) ⟨p.2.2 hy, p'.2.2 hy'⟩]
    refine (gs_compat s (𝟙 _) y (le p hy) (le p' hy')).trans ?_
    rw [gm_pull_g M Q.q.left (𝟙 _) y _ _ (le p hy) (le p' hy'), Category.id_comp]

theorem exists_sec_div [IsCommMonObj G] (M : LB Q.B.left) (hM : M.IsLB) (s : LB.Sec (M.pull Q.q.left))
    (hs : ∃ j, s.f j ≠ 0) : ∃ O : LB Q.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ Q.B O), u.IsGen) ∧
      ∃ s : LB.Sec (LB.div M O), ∃ j, s.f j ≠ 0 := by
  have := Q.q_flat
  have := Q.q_surj
  obtain ⟨χ, α, V, i, f, hV, hc, hf, ⟨p₀, hp₀⟩, hff⟩ := exists_component Q M hM s hs
  obtain ⟨N, u, hN, hw, hu⟩ := WtBundle.exists_bundle Q χ
  refine ⟨N, hN, WtBundle.exists_gen_lam Q χ N hN u hw hu, ?_⟩
  have loc : ∀ p : α × N.ι, ∃ c : Γ(Q.B.left, V p.1 ⊓ N.U p.2), ∀ x, Q.q.left x ∈ V p.1 ⊓ N.U p.2 →
      gs Q.q.left x _ c = gs (𝟙 _) x (Q.q.left ⁻¹ᵁ V p.1) (f p.1) *
        (gm (𝟙 _) x (Q.q.left ⁻¹ᵁ N.U p.2) (u p.2))⁻¹.val := fun p => by
    have l₁ : Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2) ≤ Q.q.left ⁻¹ᵁ V p.1 := fun _ k => k.1
    have l₂ : Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2) ≤ Q.q.left ⁻¹ᵁ N.U p.2 := fun _ k => k.2
    have w := ((hf p.1).res l₁).mul ((hw p.2).inv.res l₂)
    rw [add_neg_cancel] at w
    obtain ⟨c, hc⟩ := exists_app_of_isWt Q _ _ w
    refine ⟨c, fun x hx => ?_⟩
    have e := gs_pull (𝟙 _) Q.q.left x _ hx c
    rw [Category.id_comp] at e
    rw [← e, hc, gs_mul (𝟙 _) x (Q.q.left ⁻¹ᵁ (V p.1 ⊓ N.U p.2)) hx, gs_res (𝟙 _) x l₁ hx, gs_res (𝟙 _) x l₂ hx,
      gs_unit (𝟙 _) x _ (l₂ hx), map_inv]
  choose c hc' using loc
  obtain ⟨σ, hσ⟩ := exists_sec_of_refinement (LB.isLB_div hM hN) (fun p : α × N.ι => V p.1 ⊓ N.U p.2)
    (fun p => (i p.1, p.2)) (fun p => inf_le_inf_right _ (hV p.1))
    (fun y => (hc y).elim fun p hp => (exists_chart hN y).elim fun k hk => ⟨(p, k), hp, hk⟩) c
    (fun y p p' hp hp' => by
      obtain ⟨x, rfl⟩ := Q.q.left.surjective y
      apply stalkMap_injective Q.q.left x
      have hm : Q.q.left x ∈ M.U (i p.1) ⊓ N.U p.2 ⊓ (M.U (i p'.1) ⊓ N.U p'.2) :=
        ⟨⟨hV _ hp.1, hp.2⟩, hV _ hp'.1, hp'.2⟩
      have e₁ := congrArg Units.val ((WtBundle.gm_stalkMap Q.q.left x (𝟙 _) _ hm
        ((LB.div M N).g (i p.1, p.2) (i p'.1, p'.2))).trans
        (gm_div N M (Q.q.left ≫ 𝟙 _) x (i p.1, p.2) (i p'.1, p'.2) hm))
      have e₂ := hu _ (𝟙 _) x p.2 p'.2 hp.2 hp'.2
      rw [Category.comp_id] at e₁
      rw [Category.id_comp] at e₂
      rw [map_mul, ← gs_stalkMap _ x _ hp, ← gs_stalkMap _ x _ hp', hc' p x hp, hc' p' x hp',
        hff _ _ x hp.1 hp'.1, e₂]
      refine Eq.trans ?_ (congrArg (· * _) e₁).symm
      simp only [mul_inv, Units.val_mul]
      ring)
  obtain ⟨x, hx, hx0⟩ := exists_gs_ne_zero hp₀
  obtain ⟨k, hk⟩ := exists_chart hN (Q.q.left x)
  have hm : Q.q.left x ∈ (LB.div M N).U (i p₀, k) := ⟨hV _ hx, hk⟩
  refine ⟨σ, (i p₀, k), fun h => hx0 ?_⟩
  have e := hσ _ (i p₀, k) (p₀, k) hm ⟨hx, hk⟩
  rw [h, LBGerm.gs_zero (𝟙 _) (Q.q.left x) _ hm, eq_comm, Units.mul_right_eq_zero] at e
  have e' := hc' (p₀, k) x ⟨hx, hk⟩
  rw [gs_stalkMap _ x _ (show _ ∈ V p₀ ⊓ N.U k from ⟨hx, hk⟩), e, map_zero, eq_comm, Units.mul_left_eq_zero] at e'
  exact e'

end GlobalTheory.WtSec

namespace GlobalTheory

theorem exists_sec_primitive_twist : GlobalFnsSt → ∀ (A : Type) [CommRing A] [IsLocalRing A] (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (M : LB Q.B.left), M.IsLB → (∃ s : LB.Sec (M.pull Q.q.left), (∃ j, s.f j ≠ 0)) → ∃ O : LB Q.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ Q.B O), u.IsGen) ∧ ∃ s : LB.Sec (LB.div M O), (∃ j, s.f j ≠ 0) :=
  fun _ _ _ _ _ _ _ _ _ Q M hM ⟨s, hs⟩ => WtSec.exists_sec_div Q M hM s hs

end GlobalTheory
end
end

