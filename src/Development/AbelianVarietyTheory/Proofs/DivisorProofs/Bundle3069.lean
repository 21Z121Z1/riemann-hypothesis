import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_periods_projection_period_points : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R), D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D'.X] (o : D'.OAct O) (e f : O) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (φ : D'.X →+ D₀.X), IsMonHom inc → IsMonHom pr → pr ≫ inc = o.onB.act e → (∀ χ, ∃ u : LB.Gen (CmpLB D' D₀ pr (h χ) χ), Nrm u) → LBIso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ (y : D'.X) (g : GtPtF D' F), GtPtF.IsIota y g → ∃ g' : GtPtF D₀ F, Act D' D₀ pr h g g' ∧ GtPtF.IsIota (φ y) g') → (∀ y, h (φ y) = star e • f • e • y) → (∀ y, D₀.c (φ y) = D'.c y ≫ pr) ∧ ∃ w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left), w.IsGen ∧ ∀ y y' z J J', Good D'.P.L z J → Good D₀.P.L z J' → val (D₀.tau (φ y) (φ y')) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D₀.c (φ y)) (toUnit (TK R) ≫ D₀.c (φ y'))).left z J J' * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.Two.Fac.periods_of_factor | exact GlobalTheory.Mum.Two.Fac.periods_of_factor | (intros; apply GlobalTheory.Mum.Two.Fac.periods_of_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (M : HermLB p), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → ∀ (ρ : ℕ) (t₁ : ℝ), (∀ m : ℕ, 0 < m → ∃ v : Fin (ρ * m ^ D) → X.functionField, LinearIndependent ℤ v ∧ ∀ s, v s ∈ P.Bl (m * a) (m * b) (Real.exp (t₁ * m))) → (D.factorial : ℝ) * ρ ≤ gdeg M D := by
  intro hA hHS k _ X _ p D hX P a b M hRep hAmp hSemi ρ t₁ hv
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => M).1
  have hα : M.IsSelfInter (Φ (MvPolynomial.X PUnit.unit ^ (D + 1))) :=
    ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, hlim⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hHS k X p D hX P a b 0 0 M _ hRep hAmp hSemi hα
  have key := GlobalTheory.T.le_slope_of_tendsto_div_pow_of_log_lower_bound D (fun t m => P.lc (m * a) (m * b) (Real.exp (t * m)))
    (Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / ((D + 1).factorial : ℝ))
    (((D : ℝ) + 1) * gdeg M D / ((D + 1).factorial : ℝ)) ρ t₀ t₁ (Nat.cast_nonneg _) ?_ ?_
  · have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * (D.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
    have hD1 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    rw [hf, mul_div_mul_left _ _ hD1.ne', le_div_iff₀ hD] at key
    linarith
  · intro t ht
    simpa using hlim t ht
  · intro t m Q hm hQ hle
    obtain ⟨v, hli, hvB⟩ := hv m hm
    have hB := GlobalTheory.VolBr.Pair.isBallFam k X p P (m * a) (m * b)
    have hcard := GlobalTheory.T.seminormBallFamily_pow_le_encard_of_linearIndependent _ _ _ hB (ρ * m ^ D) Q (Real.exp (t₁ * m)) v (Real.exp_pos _).le hli hvB
    have hsub : P.Bl (m * a) (m * b) (((ρ * m ^ D : ℕ) : ℝ) * Q * Real.exp (t₁ * m)) ⊆
        P.Bl (m * a) (m * b) (Real.exp (t * m)) :=
      (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ hB).1 _ _ (by push_cast; linarith)
    have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P (m * a) (m * b) (Real.exp (t * m))
    have h1 : ((Q ^ (ρ * m ^ D) : ℕ) : ℕ∞) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard :=
      hcard.trans (Set.encard_le_encard hsub)
    rw [← hfin.cast_ncard_eq] at h1
    have hn : Q ^ (ρ * m ^ D) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard := by exact_mod_cast h1
    show _ ≤ Real.log _
    have hQ' : (0 : ℝ) < ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by positivity
    calc (ρ : ℝ) * (m : ℝ) ^ D * Real.log Q = Real.log ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
      _ ≤ Real.log ((P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard : ℝ) :=
          Real.log_le_log hQ' (by exact_mod_cast hn)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem finite_coheight_one_notMem_open : ∀ (X : Scheme.{0}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (U : X.Opens), genericPoint X ∈ U →
    {z : X | Order.coheight z = 1 ∧ z ∉ U}.Finite := by
  intro X _ _ U hU
  classical
  obtain ⟨S, hS, hc, hi, hUn⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint X).subset
    fun z hz => ?_
  obtain ⟨hz1, hzU⟩ := hz
  obtain ⟨T, hT, hzT⟩ := mem_sUnion.1 (hUn.le (show z ∈ (U : Set X)ᶜ from hzU))
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint X := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint X := (Specializes.antisymm e (genericPoint_specializes _)).eq
    have hm : (hi T hT).genericPoint ∈ (U : Set X)ᶜ := hUn.ge (mem_sUnion.2 ⟨T, hT, hg.mem⟩)
    exact hm (e' ▸ hU)
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRankStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_free_of_positiveDefinite_form_bounded_rank : ∀ (H : Type) [AddCommGroup H] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ r : ℕ, (∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ r) → Module.Finite ℤ H ∧ Module.Free ℤ H ∧ Module.finrank ℤ H ≤ r := by
  first | exact @GlobalTheory.finite_free_of_definite_form_of_rank_le | exact GlobalTheory.finite_free_of_definite_form_of_rank_le | (intros; apply GlobalTheory.finite_free_of_definite_form_of_rank_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdentifications
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegFibreFinite

open GlobalTheory.CechPic GlobalTheory.SiegelPull GlobalTheory.ZM.SiegPull

theorem finite_torsion {K : Type} [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (hB : IsAbelianScheme B)
    {n : ℕ} (hn : 1 ≤ n) : Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1} := by
  have := hB.smooth
  have := GlobalTheory.MulFiniteAny.isFinite_mulA K B hB n hn
  have := GlobalTheory.TorsionDivisible.finite_fibre_points (Out.mulA B n) 1
  exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ Out.mulA B n = 1) fun x => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id])

theorem finite_over_point {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hamp : Out.RelAmple A L) {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) (z : Sp K ⟶ S) (m : Pic B.left) :
    Set.Finite {φ : B.left ⟶ A.left | IsGrpPullback B A z φ ∧ pull φ (cls L hL) = m} := by
  rcases Set.eq_empty_or_nonempty {φ : B.left ⟶ A.left | IsGrpPullback B A z φ ∧ pull φ (cls L hL) = m} with
    h | ⟨φ₁, h₁, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.AmpleFiniteOrder.exists_ge_cast_ne_zero K 3
  have := hB.comm
  obtain ⟨hfin, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K B hB N hNK
  let U : Over (Sp K) := 𝟙_ (Over (Sp K))
  have hfin' : Finite {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1} := by
    refine Finite.of_surjective (fun x : {x : U ⟶ B // x ^ N = 1} =>
      (⟨pushHom h₁ U x.1, by rw [← map_pow, x.2, map_one]⟩ : {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1})) ?_
    rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := push_surjective h₁ U g
    exact ⟨⟨x, push_injective h₁ U (by rw [map_pow, hg, map_one])⟩, rfl⟩
  refine Set.finite_coe_iff.1 ?_
  refine Finite.of_injective (β := {x : U ⟶ B // x ^ N = 1} → {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1})
    (fun φ x => ⟨pushHom φ.2.1 U x.1, by rw [← map_pow, x.2, map_one]⟩) ?_
  rintro ⟨φ, h, hc⟩ ⟨φ', h', hc'⟩ e
  have e₀ : ∀ x : U ⟶ B, x ^ N = 1 → x.left ≫ φ = x.left ≫ φ' := fun x hx =>
    congrArg (fun q => q.1.left) (congrFun e ⟨x, hx⟩)
  obtain ⟨σ, hσ, eσ⟩ := GlobalTheory.SiegRigid.exists_aut h h'
  have hu : IsMonHom (σ.hom * (𝟙 B)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨ψ, hψ, eψ⟩ := hdiv _ hu fun x hx => by
    have : x ≫ σ.hom = x := Over.OverMorphism.ext (h'.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, eσ]; exact e₀ x hx) (by rw [Over.w, Over.w]))
    rw [MonObj.comp_mul, GrpObj.comp_inv, this, Category.comp_id, mul_inv_cancel]
  refine Subtype.ext (GlobalTheory.SiegRigid.eq_of_field hL hamp hB h h' (hc.trans hc'.symm) hN hNK fun Ω _ _ t x hx => ?_)
  have e₁ : x ≫ (σ.hom * (𝟙 B)⁻¹) = 1 := by
    rw [eψ, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp]
  rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, mul_inv_eq_one] at e₁
  change x.left ≫ φ = x.left ≫ φ'
  rw [← eσ, ← Category.assoc, ← Over.comp_left, e₁]

theorem pull_diag {S S' : Scheme.{0}} {A : Over S} {B : Over S'} {φ : B.left ⟶ A.left}
    {φ₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂) (m : Pic (A ⊗ A).left) :
    pull φ (pull (lift (𝟙 A) (𝟙 A)).left m) = pull (lift (𝟙 B) (𝟙 B)).left (pull φ₂ m) := by
  have e : (lift (𝟙 B) (𝟙 B)).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq hs (T := Over.mk (φ ≫ A.hom)) (T' := B) (𝟙 B.left) (𝟙 B) (𝟙 B)
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  rw [← pull_comp, ← pull_comp, e]

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

theorem point_eq (F : SFam g n ζ) {R : Type} [CommRing R] [IsLocalRing R] {B : Over (Sp R)} [GrpObj B]
    {x x' : Sp R ⟶ F.X} {φ φ' : B.left ⟶ F.univ.A.left} {φ₂ φ₂' : (G2 B).left ⟶ (G2 F.univ.A).left}
    (hs : x ≫ F.s = x' ≫ F.s) (h : IsGrpPullback B F.univ.A x φ) (h' : IsGrpPullback B F.univ.A x' φ')
    (q : IsSquare φ φ₂) (q' : IsSquare φ' φ₂')
    (hc : pull φ₂ (cls F.univ.P F.univ.isLB) = pull φ₂' (cls F.univ.P F.univ.isLB))
    (hl : ∀ a, SiegelPull.secPull h (F.univ.lev a) = SiegelPull.secPull h' (F.univ.lev a)) : x = x' := by
  obtain ⟨c, hc₀⟩ := (GlobalTheory.siegPre_pullback g n o ζ F.X (Sp R) F.s _ x F.univ rfl).1
  refine F.inj R x x' _ c hs hc₀ ?_
  obtain ⟨χ, χ₂, k, r, w, l⟩ := hc₀
  obtain ⟨e, he, ee⟩ := grpPullback_iso k h
  have k' : IsGrpPullback c.A F.univ.A x' (e.hom.left ≫ φ') :=
    ((isGrpPullback_of_iso e).comp h').congr (Category.id_comp _) rfl
  refine ⟨e.hom.left ≫ φ', (e.hom ⊗ₘ e.hom).left ≫ φ₂', k', isSquare_comp (isSquare_tensor e.hom) q', ?_,
    fun a => ?_⟩
  · have e₂ : χ₂ = (e.hom ⊗ₘ e.hom).left ≫ φ₂ := isSquare_unique r (isSquare_comp (isSquare_tensor e.hom) q) ee.symm
    refine (cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).1 ?_
    rw [(cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).2 w, cls_pull F.univ.isLB, cls_pull F.univ.isLB, e₂, pull_comp,
      pull_comp, hc]
  · have e₃ : c.lev a ≫ e.hom = SiegelPull.secPull h (F.univ.lev a) := Over.OverMorphism.ext (h.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, ee, SiegelPull.secPull_left]; exact l a) (by rw [Over.w, Over.w]))
    rw [← Category.assoc, ← Over.comp_left, e₃, hl, SiegelPull.secPull_left]

theorem finite_points (F : SFam g n ζ) (hn : 1 ≤ n) {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) (s : Sp K ⟶ Sp o) (m : Pic (G2 B).left) :
    Set.Finite {x : Sp K ⟶ F.X | x ≫ F.s = s ∧ ∃ (φ : B.left ⟶ F.univ.A.left)
      (φ₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A x φ ∧ IsSquare φ φ₂ ∧
        pull φ₂ (cls F.univ.P F.univ.isLB) = m} := by
  have := finite_torsion B hB hn
  have := hB.comm
  refine Set.finite_coe_iff.1 ?_
  have H := fun x : {x : Sp K ⟶ F.X | x ≫ F.s = s ∧ ∃ (φ : B.left ⟶ F.univ.A.left)
      (φ₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A x φ ∧ IsSquare φ φ₂ ∧
        pull φ₂ (cls F.univ.P F.univ.isLB) = m} => x.2.2
  choose φ φ₂ h q hc using H
  refine Finite.of_injective (β := (Fin g ⊕ Fin g) → {y : 𝟙_ (Over (Sp K)) ⟶ B // y ^ n = 1})
    (fun x i => ⟨SiegelPull.secPull (h x) (F.univ.lev (Pi.single i 1)), push_injective (h x) _ (by
      rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, F.univ.lev_tors, MonObj.comp_one])⟩) ?_
  intro x x' e
  refine Subtype.ext (point_eq F (x.2.1.trans x'.2.1.symm) (h x) (h x') (q x) (q x') ((hc x).trans (hc x').symm) ?_)
  let p := fun y => (AddMonoidHom.mk' (fun a => Additive.ofMul (SiegelPull.secPull (h y) (F.univ.lev a))) fun a b => by
      rw [← ofMul_mul]
      exact congrArg _ (push_injective (h y) _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', F.univ.lev_add, MonObj.comp_mul])) :
    (Fin g ⊕ Fin g → ℤ) →+ Additive (𝟙_ (Over (Sp K)) ⟶ B))
  have hp : p x = p x' := AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int
    (congrArg (fun z => Additive.ofMul z.1) (congrFun e i))
  exact fun a => congrArg Additive.toMul (DFunLike.congr_fun hp a)

theorem finite_identifications : ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ'), 1 ≤ n' → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (x₀ : Sp K ⟶ F'.X) (φ₀ : B.left ⟶ F'.univ.A.left) (φ₀₂ : (G2 B).left ⟶ (G2 F'.univ.A).left), IsGrpPullback B F'.univ.A x₀ φ₀ → IsSquare φ₀ φ₀₂ → ∀ p₀ : Sp K ⟶ B.left, Set.Finite {P' : Sp K ⟶ F'.univ.A.left | ∃ (x' : Sp K ⟶ F'.X) (φ : B.left ⟶ F'.univ.A.left) (φ₂ : (G2 B).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = x₀ ≫ F'.s ∧ IsGrpPullback B F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ P' = p₀ ≫ φ} := by
  intro o _ ζ g n F hn K _ _ B _ x₀ φ₀ φ₀₂ h₀ _ p₀
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab h₀
  let m := pull φ₀₂ (cls F.univ.P F.univ.isLB)
  have h₁ := finite_points F hn hB (x₀ ≫ F.s) m
  have h₂ := fun x => finite_over_point (pull_isLB F.univ.isLB _) F.princ.1 hB x (pull (lift (𝟙 B) (𝟙 B)).left m)
  refine ((h₁.biUnion fun x _ => h₂ x).image (p₀ ≫ ·)).subset ?_
  rintro _ ⟨x, φ, φ₂, hs, h, q, w, rfl⟩
  have e : pull φ₂ (cls F.univ.P F.univ.isLB) = m := by
    have := (cls_eq_iff (pull_isLB F.univ.isLB _) (pull_isLB F.univ.isLB _)).2 w
    rw [cls_pull F.univ.isLB, cls_pull F.univ.isLB] at this
    exact this.symm
  refine ⟨φ, Set.mem_biUnion (x := x) ⟨hs, φ, φ₂, h, q, e⟩ ⟨h, ?_⟩, rfl⟩
  rw [← e, ← pull_diag q]
  exact congrArg _ (cls_pull F.univ.isLB _ _)

end GlobalTheory.SiegFibreFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsFixedFrobeniusPowerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_fixed_frobenius_power : ∀ (K : Type) [Field K] [Fintype K] (σ : Gal K) (X : Over (Sp K)) (s : Finset (ptOver K (AlgebraicClosure K) ⟶ X)), LocallyOfFiniteType X.hom → ∃ m : ℕ, ∀ x ∈ s, specAut σ ≫ x = specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) ≫ x := by
  first | exact @GlobalTheory.AV.GalPow.exists_frob_pow_on_finset | exact GlobalTheory.AV.GalPow.exists_frob_pow_on_finset | (intros; apply GlobalTheory.AV.GalPow.exists_frob_pow_on_finset; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SmallFin

theorem smallSec_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ M : HermLB p, M.smallSec.Finite := by
  intro k _ X _ p D hX M
  obtain ⟨P, hL, -⟩ := GlobalTheory.VolBr.exists_pair M M
  subst hL
  have hrep : P.Rep 1 0 P.L := (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  obtain ⟨e, he, hrange, hnorm, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P 1 0 P.L hrep
  have hfin : (P.Bl 1 0 1).Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  refine (hfin.preimage he.injOn).subset ?_
  intro u hu
  refine ⟨?_, fun σ y => ?_⟩
  · have hm : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at hm
    exact hm
  have h0 : 0 ≤ P.nu 1 0 σ y (e u) := by
    unfold Pair.nu; positivity
  have h1 : P.nu 1 0 σ y (e u) ^ 2 ≤ 1 := by
    rw [hnorm]; exact hu σ y
  exact (pow_le_one_iff_of_nonneg h0 two_ne_zero).1 h1

end GlobalTheory.SmallFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenspacesOfSeparableMinpoly
section
open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.EigSum

theorem finrank_eigenspaces_of_separable_minpoly
    (Ω V : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] (T : Module.End Ω V) (f : Polynomial Ω) (hm : f.Monic)
    (hs : f.Separable) (h0 : Polynomial.aeval T f = 0)
    (hmin : ∀ g : Polynomial Ω, Polynomial.aeval T g = 0 → f ∣ g) :
    ∑ z ∈ f.roots.toFinset, Module.finrank Ω (T.eigenspace z) = Module.finrank Ω V ∧
      ∀ z ∈ f.roots, T.eigenspace z ≠ ⊥ := by
  have hf : f = minpoly Ω T := by
    apply Polynomial.eq_of_monic_of_associated hm (minpoly.monic (Algebra.IsIntegral.isIntegral T))
    exact associated_of_dvd_dvd (hmin _ (minpoly.aeval Ω T)) (minpoly.dvd Ω T h0)
  have hroot : ∀ z, T.HasEigenvalue z ↔ z ∈ f.roots := by
    intro z
    rw [Module.End.hasEigenvalue_iff_isRoot, ← hf, Polynomial.mem_roots hm.ne_zero]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0
  refine ⟨?_, fun z hz => (hroot z).2 hz⟩
  set s := f.roots.toFinset
  let N : s → Submodule Ω V := fun z => T.eigenspace z
  have hind : iSupIndep N :=
    iSupIndep.comp (Module.End.eigenspaces_iSupIndep T) Subtype.val_injective
  have htop : ⨆ z, N z = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top T
    simp only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
    rw [eq_top_iff, ← h1]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ s
    · exact le_iSup N ⟨μ, hμ⟩
    · have : ¬ T.HasEigenvalue μ := by
        rw [hroot]; simpa [s] using hμ
      rw [Module.End.hasEigenvalue_iff, not_not] at this
      simp [this]
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint).finrank_eq,
    Module.finrank_directSum]
  exact (Finset.sum_coe_sort s (fun z => Module.finrank Ω (T.eigenspace z))).symm

end GlobalTheory.EigSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKerIdealDvd
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham (spOver spOver_comp)
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

variable {k : Type} [Field k] {A B : AbVar k}

def KerPow (f : A ⟶ B) (c : ℕ) (H : Type) [CommRing H] [Algebra k H] (i : ptOver k H ⟶ A.X) : Prop :=
  (i ≫ f.hom = 1 ∧ i ^ c = 1) ∧
    ∀ (R : Type) [CommRing R] [Algebra k R] (x : ptOver k R ⟶ A.X), x ≫ f.hom = 1 → x ^ c = 1 →
      ∃! φ : H →ₐ[k] R, spMap φ.toRingHom ≫ i.left = x.left

theorem finrank_eq_of_kerPow {f : A ⟶ B} {c c' : ℕ} {H H' : Type} [CommRing H] [Algebra k H] [CommRing H']
    [Algebra k H'] {i : ptOver k H ⟶ A.X} {i' : ptOver k H' ⟶ A.X} (h : KerPow f c H i) (h' : KerPow f c' H' i')
    (e : ∀ (R : Type) [CommRing R] [Algebra k R] (x : ptOver k R ⟶ A.X), x ≫ f.hom = 1 → (x ^ c = 1 ↔ x ^ c' = 1)) :
    Module.finrank k H = Module.finrank k H' := by
  obtain ⟨φ, hφ, -⟩ := h.2 H' i' h'.1.1 ((e H' i' h'.1.1).2 h'.1.2)
  obtain ⟨ψ, hψ, -⟩ := h'.2 H i h.1.1 ((e H i h.1.1).1 h.1.2)
  have h1 : ψ.comp φ = AlgHom.id k H := by
    obtain ⟨χ, -, hχ⟩ := h.2 H i h.1.1 h.1.2
    refine (hχ _ ?_).trans (hχ _ ?_).symm
    · change spMap ((ψ : H' →+* H).comp (φ : H →+* H')) ≫ i.left = i.left
      rw [Cris.spMap_comp, Category.assoc]
      exact (congrArg (spMap (ψ : H' →+* H) ≫ ·) hφ).trans hψ
    · change spMap (RingHom.id H) ≫ i.left = i.left
      rw [Cris.spMap_id, Category.id_comp]
  have h2 : φ.comp ψ = AlgHom.id k H' := by
    obtain ⟨χ, -, hχ⟩ := h'.2 H' i' h'.1.1 h'.1.2
    refine (hχ _ ?_).trans (hχ _ ?_).symm
    · change spMap ((φ : H →+* H').comp (ψ : H' →+* H)) ≫ i'.left = i'.left
      rw [Cris.spMap_comp, Category.assoc]
      exact (congrArg (spMap (φ : H →+* H') ≫ ·) hψ).trans hφ
    · change spMap (RingHom.id H') ≫ i'.left = i'.left
      rw [Cris.spMap_id, Category.id_comp]
  exact (AlgEquiv.ofAlgHom φ ψ h2 h1).toLinearEquiv.finrank_eq

theorem pow_eq_one_of_comp {f : A ⟶ B} {g : B ⟶ A} {N : ℕ} (h : f ≫ g = N • 𝟙 A) {T : Over (Sp k)}
    (x : T ⟶ A.X) (hx : x ≫ f.hom = 1) : x ^ N = 1 := by
  have e := congrArg (fun u : A ⟶ A => x ≫ u.hom) h
  simp only [comp_hom, nsmul_hom, id_hom] at e
  rw [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at e
  exact e.symm

section Tower

variable {p : ℕ} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B) (n : ℕ)

def kerPt : ptOver k (G.A n ⧸ kerIdeal ((t.map t' f.hom).app n)) ⟶ A.X :=
  spOver (Ideal.Quotient.mkₐ k (kerIdeal ((t.map t' f.hom).app n))) ≫ t.y n

theorem comp_eq_one_iff {R : Type} [CommRing R] [Algebra k R] (φ : G.A n →ₐ[k] R) :
    (spOver φ ≫ t.y n) ≫ f.hom = 1 ↔ kerIdeal ((t.map t' f.hom).app n) ≤ RingHom.ker φ := by
  rw [kerIdeal_le_ker_iff _ φ, Category.assoc, ← t.map_y t' f.hom n, ← Category.assoc, spOver_comp,
    t'.eq_one_iff]
  rfl

theorem kerPow_kerPt : KerPow f (p ^ n) _ (kerPt t t' f n) := by
  set I := kerIdeal ((t.map t' f.hom).app n)
  refine ⟨⟨(comp_eq_one_iff t t' f n _).2 ?_, (t.exists_iff n _).1 ⟨_, rfl⟩⟩, ?_⟩
  · exact fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  · intro R _ _ x hx hp
    obtain ⟨φ, hφ⟩ := t.surj n R x hp
    have hI : I ≤ RingHom.ker φ := (comp_eq_one_iff t t' f n φ).1 (hφ ▸ hx)
    refine ⟨Ideal.Quotient.liftₐ I φ (fun a ha => hI ha), ?_, fun ψ hψ => ?_⟩
    · change (spOver (Ideal.Quotient.liftₐ I φ (fun a ha => hI ha)) ≫ kerPt t t' f n).left = x.left
      rw [kerPt, ← Category.assoc, spOver_comp]
      exact congrArg Over.Hom.left ((congrArg (spOver · ≫ t.y n) (AlgHom.ext fun a => rfl)).trans hφ)
    · have h1 : spOver (ψ.comp (Ideal.Quotient.mkₐ k I)) ≫ t.y n = x := by
        rw [← spOver_comp, Category.assoc]
        exact Over.OverMorphism.ext hψ
      have h2 := t.inj n R _ _ (h1.trans hφ.symm)
      exact Ideal.Quotient.algHom_ext k (h2.trans (AlgHom.ext fun a => rfl))

end Tower

theorem finrank_quot_kerIdeal_dvd {p : ℕ} {G H : PDivGroup p k} (φ : G ⟶ H) (n : ℕ) :
    Module.finrank k (G.A n ⧸ kerIdeal (φ.app n)) ∣ p ^ (n * G.height) := by
  have h := finrank_eq_ker_mul_range k (G.A n) (H.A n) (φ.app n)
  have h2 : Module.finrank k (G.A n) = p ^ (n * G.height) := by
    have h3 := G.fibreDim_eq n ⟨⊥, Ideal.isPrime_bot⟩
    rw [fibreDim, Module.finrank_baseChange] at h3
    exact h3
  exact ⟨_, h2 ▸ h⟩

end GlobalTheory.AV.KerPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeFderivLtOfNotDominantChartsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_fderiv_lt_of_not_dominant_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (A : FinHolAtlas D (CxPts p σ)) (A' : FinHolAtlas D (CxPts q σ)), IsAlgAtlas A → IsAlgAtlas A' → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) ≠ genericPoint X → ∀ j l, ∀ y ∈ (A'.chart j).target, PtsOver.map π hπ (spMap σ) ((A'.chart j).symm y) ∈ (A.chart l).source → Module.finrank ℂ (LinearMap.range (fderiv ℂ (A.chart l ∘ PtsOver.map π hπ (spMap σ) ∘ (A'.chart j).symm) y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) < D := by
  first | exact @GlobalTheory.finrank_range_fderiv_lt_of_not_dominant | exact GlobalTheory.finrank_range_fderiv_lt_of_not_dominant | (intros; apply GlobalTheory.finrank_range_fderiv_lt_of_not_dominant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullbackStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_chern_form_pullback : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ L : HermLB p, fld _ (c1F hY σ (L.pull π w)) = pullF hX hY σ π w (fld _ (c1F hX σ L)) := by
  first | exact @GlobalTheory.ChernPull.c1F_pull_eq_pullF_c1F | exact GlobalTheory.ChernPull.c1F_pull_eq_pullF_c1F | (intros; apply GlobalTheory.ChernPull.c1F_pull_eq_pullF_c1F <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernTensorAddStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChern_tensor_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L M : HermLB p, c1F hX σ (L.tens M) = c1F hX σ L + c1F hX σ M := by
  first | exact @GlobalTheory.LineForm.c1F_tens | exact GlobalTheory.LineForm.c1F_tens | (intros; apply GlobalTheory.LineForm.c1F_tens <;> assumption)
end

