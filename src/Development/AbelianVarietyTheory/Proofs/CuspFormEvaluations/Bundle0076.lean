import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0073
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProducts
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ArchimedeanFlatDecompositionIndexing
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.UpperRecord

theorem finrank_le_of_parts {Y ι : Type} {Z : ι → Type} (V : Submodule ℂ (Y → ℂ)) (e : Y ≃ Σ k, Z k)
    (d : ι → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (hb : ∀ (k : ι) (m : ℕ) (g : Fin m → V),
      LinearIndependent ℂ (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) → m ≤ d k * C) :
    Module.finrank ℂ V ≤ δ * C := by
  classical
  let ρ : ∀ k, V →ₗ[ℂ] (Z k → ℂ) := fun k =>
    (LinearMap.funLeft ℂ ℂ fun z : Z k => e.symm ⟨k, z⟩).comp V.subtype
  have hr : ∀ k, Module.rank ℂ (LinearMap.range (ρ k)) ≤ (d k * C : ℕ) := fun k => by
    refine rank_le fun s hs => ?_
    have hs' := (hs.comp s.equivFin.symm s.equivFin.symm.injective).map' (LinearMap.range (ρ k)).subtype
      (Submodule.ker_subtype _)
    choose g hg using fun q : Fin s.card => (s.equivFin.symm q).1.2
    refine hb k s.card g ?_
    have heq : (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) = _ := funext hg
    rw [heq]
    exact hs'
  have hfin : ∀ k, Module.Finite ℂ (LinearMap.range (ρ k)) := fun k =>
    Module.rank_lt_aleph0_iff.1 ((hr k).trans_lt (Cardinal.natCast_lt_aleph0))
  have hfr : ∀ k, Module.finrank ℂ (LinearMap.range (ρ k)) ≤ d k * C := fun k =>
    Module.finrank_le_of_rank_le (hr k)
  let s : Finset ι := Finset.univ.image fun q => (en q).1
  have hs : ∀ k, k ∉ s → d k = 0 := fun k hk => by
    by_contra h0
    exact hk (Finset.mem_image.2 ⟨en.symm ⟨k, ⟨0, Nat.pos_of_ne_zero h0⟩⟩, Finset.mem_univ _, by simp⟩)
  let Φ : V →ₗ[ℂ] (∀ k : s, LinearMap.range (ρ k)) := LinearMap.pi fun k => (ρ k).rangeRestrict
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have hk : ∀ k, ρ k g = 0 := fun k => by
      by_cases hk : k ∈ s
      · exact congrArg Subtype.val (congrFun hg ⟨k, hk⟩)
      · have h0 : Module.finrank ℂ (LinearMap.range (ρ k)) = 0 := by
          have := hfr k
          rw [hs k hk] at this
          omega
        have := Submodule.finrank_eq_zero.1 h0
        exact (Submodule.eq_bot_iff _).1 this _ ⟨g, rfl⟩
    ext y
    have := congrFun (hk (e y).1) (e y).2
    simpa [ρ, LinearMap.funLeft_apply] using this
  have hsum : ∑ k : s, d k ≤ δ := by
    have hinj : Function.Injective fun p : Σ k : s, Fin (d k) => en.symm ⟨p.1.1, p.2⟩ := by
      rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, a'⟩ hp
      have := en.symm.injective hp
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 this
      obtain rfl := eq_of_heq h2
      rfl
    simpa using Fintype.card_le_of_injective _ hinj
  calc Module.finrank ℂ V ≤ Module.finrank ℂ (∀ k : s, LinearMap.range (ρ k)) :=
        LinearMap.finrank_le_finrank_of_injective hΦ
    _ = ∑ k : s, Module.finrank ℂ (LinearMap.range (ρ k)) := Module.finrank_pi_fintype ℂ
    _ ≤ ∑ k : s, d k * C := Finset.sum_le_sum fun k _ => hfr k
    _ = (∑ k : s, d k) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ δ * C := Nat.mul_le_mul_right _ hsum

theorem upper : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → Module.finrank ℂ (R.sp (addL wF wL Tn) Set.univ) ≤ δ * (Tn + 2 * WeightFamilies.dimY D j + 6).choose (WeightFamilies.dimY D j) := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _
  refine finrank_le_of_parts _ e (fun k => (Fl.Fl k).δ) _ δ en fun k m g hg => ?_
  choose f hf hgf using fun q => (GlobalTheory.T.mem_span_cuspReadings_iff_components D T h j hj n R e hR (addL wF wL Tn)).1 (g q).1 (g q).2
  have hw := (GlobalTheory.T.componentModelWeight_dimension_dictionary D T h j hj k).2.2.1 wF wL Tn
  have := GlobalTheory.UpperModel.upper _ _ _ (A.Xa k) (Fl.Fl k) m (fun q => f q k) (fun q => by
    rw [A.hF, A.hL, A.hT, ← hw]
    exact (hf q k).1.1) (fun u hu => by
    funext q
    refine Fintype.linearIndependent_iff.1 hg u ?_ q
    funext z
    have := hu z.1 z.2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hgf q, e.apply_symm_apply])
  rwa [A.hT, A.dim] at this

end GlobalTheory.UpperRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardPeriodSpacesFamilyUniformisationLe
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace PeriodSpaceCount

theorem exists_injective_pi {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] {r : ℕ} (hr : Module.finrank R M = r) :
    ∃ φ : M →ₗ[R] (Fin r → R), Function.Injective φ := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) hr.ge
  have h1 := (Submodule.span R (Set.range v)).finrank_quotient_add_finrank
  rw [finrank_span_eq_card hv, Fintype.card_fin, hr] at h1
  have h2 : Module.IsTorsion R (M ⧸ Submodule.span R (Set.range v)) :=
    Module.finrank_eq_zero_iff_isTorsion.1 (by omega)
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors h2
  have h3 : ∀ m : M, (c • (LinearMap.id : M →ₗ[R] M)) m ∈ Submodule.span R (Set.range v) := fun m => by
    have h3 := Submodule.mem_annihilator.1 hc (Submodule.Quotient.mk m) trivial
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h3
  refine ⟨(Module.Basis.span hv).equivFun.toLinearMap ∘ₗ LinearMap.codRestrict _ _ h3,
    (Module.Basis.span hv).equivFun.injective.comp fun x y h => ?_⟩
  exact smul_right_injective M (nonZeroDivisors.ne_zero hc0) (congrArg Subtype.val h)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_generators (D : Datum H) {k : ℕ} (hk : 0 < k) :
    ∃ x : Fin (D.p + D.q) → D.La, ∀ m : D.La, ∃ (c : Fin (D.p + D.q) → 𝓞 E) (m' : D.La),
      m = ∑ i, c i • x i + k • m' := by
  have := D.fin
  have := D.proj
  obtain ⟨φ, hφ⟩ := exists_injective_pi D.rank
  obtain ⟨x, hx⟩ := BoundedBasis.exists_generators_mod_smul (a := (k : 𝓞 E))
    (Nat.cast_ne_zero.2 hk.ne') _ D.La φ hφ
  refine ⟨x, fun m => ?_⟩
  obtain ⟨c, m', h⟩ := hx m
  exact ⟨c, m', by rw [h, Nat.cast_smul_eq_nsmul]⟩

def Isometric (D D' : Datum H) : Prop :=
  ∃ gam : D.La ≃ₗ[𝓞 E] D'.La, ∀ a b, D'.EF (gam a) (gam b) = D.EF a b

theorem Isometric.refl (D : Datum H) : Isometric D D := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem Isometric.symm {D D' : Datum H} (h : Isometric D D') : Isometric D' D := by
  obtain ⟨gam, h⟩ := h
  exact ⟨gam.symm, fun a b => by rw [← h]; simp⟩

theorem Isometric.trans {D D' D'' : Datum H} (h : Isometric D D') (h' : Isometric D' D'') :
    Isometric D D'' := by
  obtain ⟨gam, h⟩ := h
  obtain ⟨gam', h'⟩ := h'
  exact ⟨gam.trans gam', fun a b => by rw [← h, ← h']; rfl⟩

theorem card_isometric_le {D D₀ : Datum H} (h₀ : D₀.p + D₀.q = D.p + D.q) {k : ℕ} (hk : 0 < k)
    {n : ℕ} (Di : Fin n → Datum H) (t : ∀ i, D.La →ₗ[𝓞 E] (Di i).La)
    (hmatch : ∀ (i j : Fin n) (gam : (Di i).La ≃ₗ[𝓞 E] (Di j).La),
      (∀ a b, (Di j).EF (gam a) (gam b) = (Di i).EF a b) →
      (∀ a, ∃ e, gam (t i a) = t j a + k • e) → i = j)
    (s : Finset (Fin n)) (hs : ∀ i ∈ s, Isometric (Di i) D₀) :
    s.card ≤ k ^ (2 * FD.fdeg E * (D.p + D.q) ^ 2) := by
  classical
  have := D₀.fin
  have : Module.Finite ℤ D₀.La := Module.Finite.trans (𝓞 E) D₀.La
  have := datum_free_int D₀
  let K : AddSubgroup D₀.La := (nsmulAddMonoidHom k : D₀.La →+ D₀.La).range
  have hK : Nat.card (D₀.La ⧸ K) = k ^ Module.finrank ℤ D₀.La :=
    AddSubgroup.index_range_nsmul D₀.La k
  have : Finite (D₀.La ⧸ K) := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨x, hx⟩ := exists_generators D hk
  choose gam hgam using hs
  let F : s → Fin (D.p + D.q) → D₀.La ⧸ K := fun i c => QuotientAddGroup.mk (gam i.1 i.2 (t i.1 (x c)))
  have hF : Function.Injective F := by
    intro i j hij
    refine Subtype.ext (hmatch i.1 j.1 ((gam i.1 i.2).trans (gam j.1 j.2).symm) (fun a b => ?_)
      fun a => ?_)
    · rw [← hgam j.1 j.2, ← hgam i.1 i.2]
      simp
    · have h1 : ∀ c, ∃ e, gam i.1 i.2 (t i.1 (x c)) = gam j.1 j.2 (t j.1 (x c)) + k • e := fun c => by
        obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 (congrFun hij c).symm
        exact ⟨e, by rw [show k • e = _ from he, add_neg_cancel_left]⟩
      choose e he using h1
      obtain ⟨c, m', rfl⟩ := hx a
      refine ⟨(gam j.1 j.2).symm (∑ d, c d • e d + gam i.1 i.2 (t i.1 m') - gam j.1 j.2 (t j.1 m')), ?_⟩
      apply (gam j.1 j.2).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, map_add, map_nsmul, map_sum,
        map_smul, he, smul_add, smul_sub, Finset.sum_add_distrib, Finset.smul_sum, smul_comm k]
      abel
  have h2 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_fun, hK, datum_finrank_int, h₀,
    Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul] at h2
  refine h2.trans (le_of_eq ?_)
  congr 1
  unfold FD.fdeg
  ring

theorem exists_representatives {n : ℕ} (Di : Fin n → Datum H) :
    ∃ (m : ℕ) (rep : Fin m → Fin n), (∀ c d, Isometric (Di (rep c)) (Di (rep d)) → c = d) ∧
      ∀ i, ∃ c, Isometric (Di i) (Di (rep c)) := by
  let S : Setoid (Fin n) := ⟨fun i j => Isometric (Di i) (Di j),
    fun _ => Isometric.refl _, Isometric.symm, Isometric.trans⟩
  let e := Finite.equivFin (Quotient S)
  refine ⟨_, fun c => (e.symm c).out, fun c d h => ?_, fun i => ⟨e (Quotient.mk S i), ?_⟩⟩
  · exact e.symm.injective (Quotient.out_equiv_out.1 h)
  · simp only [Equiv.symm_apply_apply]
    exact Isometric.symm (Quotient.mk_out (s := S) i)

end PeriodSpaceCount

open PeriodSpaceCount in

theorem familyUnif_card_le : GlobalTheory.Published.HasseNormSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ U : FamilyUnif Xo σ ty, ∀ (r : ℕ), r = D.p + D.q → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → (U.n : ℝ) ≤ (l.M' : ℝ) ^ (2 * FD.fdeg E * r ^ 2) * ((1 + 2 * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2) * (r * max 1 ((2 * FD.fdeg E * r : ℝ) ^ 4 * FD.dE E ^ 2 / (4 * FD.fdeg E))) ^ (2 * FD.fdeg E * r ^ 2)) ∧ ∀ L : ℝ, 16 ≤ FD.fdeg E → 2 ≤ L → Real.log (FD.dE E) ≤ 4 * FD.fdeg E * L → Real.log r ≤ L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log l.M' ≤ 30 * L → Real.log U.n ≤ 41 * (FD.fdeg E * r * L) ^ 2 := by
  intro hN hT hL E _ _ _ H D l Xo σ g ty h1 hσ hty U r hr ξ AA hξ hξ0 hfg hA0 hAA
  classical
  have hk : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  obtain ⟨m, rep, hrep, hcls⟩ := exists_representatives U.Di
  have hm := GlobalTheory.T.card_nonisometric_cmTorusData_le hN E H D.p D.q r hr ξ AA hξ hξ0 hfg hA0 hAA m (fun c => U.Di (rep c))
    (fun c => U.sig _) fun c d gam h => hrep c d ⟨gam, h⟩
  have hn : U.n ≤ m * l.M' ^ (2 * FD.fdeg E * r ^ 2) := by
    have h2 : (Finset.univ : Finset (Fin U.n)) ⊆ (Finset.univ : Finset (Fin m)).biUnion
        fun c => Finset.univ.filter fun i => Isometric (U.Di i) (U.Di (rep c)) := fun i _ => by
      obtain ⟨c, hc⟩ := hcls i
      exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩
    have h3 := (Finset.card_le_card h2).trans (Finset.card_biUnion_le_card_mul _ _
      (l.M' ^ (2 * FD.fdeg E * r ^ 2)) fun c _ => by
        rw [hr]
        exact card_isometric_le (D₀ := U.Di (rep c)) (by rw [(U.sig _).1, (U.sig _).2]) hk U.Di U.t
          (GlobalTheory.T.familyUnif_index_eq_of_marked_latticeIsometry hT hL E H D l Xo σ g ty h1 hσ hty U) _ fun i hi => (Finset.mem_filter.1 hi).2)
    simpa using h3
  have hmain := le_trans (b := (l.M' : ℝ) ^ (2 * FD.fdeg E * r ^ 2) * m) (a := (U.n : ℝ))
    (by rw [mul_comm]; exact_mod_cast hn) (mul_le_mul_of_nonneg_left hm (by positivity))
  refine ⟨hmain, fun L hf hL2 hd hrL hfL hM => ?_⟩
  have h := hmain.trans (ClassCount.pow_mul_bound_le_exp (FD.fdeg E) r (d := FD.dE E) hf hL2
    (abs_nonneg _) hd hrL hfL (Nat.cast_nonneg _) hM)
  have h0 := sq_nonneg (FD.fdeg E * r * L)
  have h' : (0 : ℝ) < U.n := by exact_mod_cast U.n_pos
  linarith [(Real.log_le_iff_le_exp h').2 h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpanStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_vanishing_at_points_mul_pow_mem_span : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  first | exact @GlobalTheory.Shares.VanDiv.vanishing_division | exact GlobalTheory.Shares.VanDiv.vanishing_division | (intros; apply GlobalTheory.Shares.VanDiv.vanishing_division <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingLowCoeffMemLeadingAddDeepSpanStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_vanishing_low_coeff_mem_leading_add_deep_span : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → (∀ F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tn c j (addL wF wL Tn), ∀ k : (T.U j T.σ₀).Comp, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → Submodule.span ℂ (Set.range (vals xs θ)) = ⊤ → R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn)) ≤ Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ)) ⊔ R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn) := by
  first | exact @GlobalTheory.Containment.main | exact GlobalTheory.Containment.main | (intros; apply GlobalTheory.Containment.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeffStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_lower_bound_cuspForm_vanishing_low_coeff : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  first | exact @GlobalTheory.LowerBound.lower_bound | exact GlobalTheory.LowerBound.lower_bound | (intros; apply GlobalTheory.LowerBound.lower_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProductsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingProducts_independent_modulo_deepProducts : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → LinearIndependent ℂ (vals xs θ) → LinearIndependent ℂ (R.lead w t Tn (a0 D j Tn) θ) ∧ Disjoint (Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ))) (R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn)) := by
  first | exact @GlobalTheory.Shares.LeadDeep.main | exact GlobalTheory.Shares.LeadDeep.main | (intros; apply GlobalTheory.Shares.LeadDeep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyHeightOneSpectrumRingOfIntegers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem nonempty_heightOneSpectrum_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    Nonempty (HeightOneSpectrum (𝓞 K)) := by

  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩

theorem shareRhoP_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ) (CR c : ℝ) (δ : ℕ) (xs : Fin δ → R.Y), AnFacts R w t ka wF T (WeightFamilies.MggK B CR T c j ka) xs → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ T → LatAt B j ka → ShareRhoP (D := D) (j := j) T (WeightFamilies.rhoP B CR T c j ka) (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF N w R t T CR c δ xs hA hD hT hL
  obtain ⟨la⟩ := nonempty_heightOneSpectrum_ringOfIntegers B.KO

  have hdim : ∀ M : Submodule B.KO (B.Cusp j ka),
      Module.finrank ℂ (R.sp ka M) = Module.finrank B.KO M := fun M =>
    ((GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t).2.2.2.2.2.2.2 ka M).2
  have hspan : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ := hL.span_eq_top

  have hd : X.rk ka (B.Mlat j ka) = Module.finrank B.KO (B.Cusp j ka) := by
    unfold PJ.rk
    rw [hspan, finrank_top]
  have hup : Module.finrank ℂ (R.sp ka Set.univ) = Module.finrank B.KO (B.Cusp j ka) := by
    have h := hdim ⊤
    rwa [Submodule.top_coe, finrank_top] at h

  have hsum := Submodule.finrank_quotient_add_finrank (WeightFamilies.MggK B CR T c j ka)
  have hq := rhoP_eq_finrank B CR T c j ka hspan
  have hlo := hA.lower
  rw [hdim] at hlo
  have key := (GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair (WeightFamilies.dimY D j) T).2 δ (X.rk ka (B.Mlat j ka)) (WeightFamilies.rhoP B CR T c j ka) hD hT
    (by rw [hd, ← hup]; exact hA.upper)
  exact key.2 (by rw [hq, hd, ← hsum]; omega)

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PhiFDEqZeroAtLastIndex
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem phiFD_eq_zero_at_last_index : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), j = D.R.m → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp), ∀ x ∈ ((T.U j σ).X k).dom, I2.phiFD ((T.U j σ).X k) (I2.th (E := D.host.E) q R0) x = 0 := by
  intro D T h j hj hjm DF q R0 hrun σ hσ k x hx
  have hu := h.unf j hj σ hσ
  have hq0 : (T.Q.Dw j).q = 0 := by
    rw [(h.pins.2.2.2 j hj).2.1, hjm]
    exact Nat.sub_self _
  have hp0 : ((T.U j σ).X k).p0 = 0 := ((hu.2.1 k).1).trans hq0
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hu k ⟨x, hx⟩
  have hint : ∀ u ∈ ((T.U j σ).X k).Λ, ∀ v ∈ ((T.U j σ).X k).Λ, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (((T.U j σ).X k).ξ0 * FD.herm ((T.U j σ).X k).Gm u v) = z := by
    intro u hu' v hv'
    have hEF := W.isom k ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)
    simp only [LinearEquiv.apply_symm_apply] at hEF
    refine ⟨-((W.F.Di (W.ik k)).EF ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)), ?_⟩
    rw [Int.cast_neg, hEF, neg_mul, map_neg, neg_neg]
  obtain ⟨A, -⟩ := GlobalTheory.T.exists_torusWithSign_uniformisationFrame _ _ _ _ _ _ _ _ (T.U j σ) k ⟨x, hx⟩ W
  obtain ⟨τ0⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((T.U j σ).X k).Ψ := by
    by_cases h1 : τ0 ∈ ((T.U j σ).X k).Ψ
    · exact ⟨τ0, h1⟩
    · refine ⟨NumberField.ComplexEmbedding.conjugate τ0, ?_⟩
      rw [((T.U j σ).X k).cmType]
      simpa using h1
  have hpos := A.dim_pos ⟨τ, hτ⟩
  have hneg := A.dim_neg ⟨τ, hτ⟩
  have hsum := A.T.dim_conj τ
  have hr : A.T.r = D.R.r := by
    simp only at hpos hneg
    omega
  obtain ⟨P, hPq, hPR, -⟩ := hrun A.T hr ⟨τ, by simp only at hpos; omega⟩
  have hr0 : 0 < D.R.r := by
    have h2m := D.R.two_le_m
    show 0 < D.R.k + D.R.m - 1
    omega
  refine (GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero D.host.E D.R.r ((T.U j σ).X k) hr0 hp0 hint x hx).2 q R0
    ?_ ?_ ?_
  · have h16 := P.hrd
    linarith
  · have h1q := P.hq
    omega
  · have hb := P.C2
    rwa [hPq, hPR] at hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorsScaledThetaLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGenerators_scaled_thetaLattice : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (w : WeightFamilies.Wt D j) (s : 𝓞 B.KO) (Sh : Finset (B.Cusp j w)) (a b : ℝ), s ≠ 0 → 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (s : B.KO)‖ ≤ a) → (∀ g ∈ Sh, g ∈ X.shortTh w ∧ ∀ σ, Real.log (B.supN j w σ g) ≤ b) → Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ → ShortG X w (X.Thc s w) (a + b + lamStar D * w.size) := by
  first | exact @GlobalTheory.RunIn.shortG_scaled | exact GlobalTheory.RunIn.shortG_scaled | (intros; apply GlobalTheory.RunIn.shortG_scaled <;> assumption)
end

