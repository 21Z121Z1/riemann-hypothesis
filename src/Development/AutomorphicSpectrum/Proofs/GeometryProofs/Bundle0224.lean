import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0221
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralNthRootTestModelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0166
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0170
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0168
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0103
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0163
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0161
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveRootHodgeCpt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0213
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0217
import Development.WeilBound.CoreStatements.HodgeTatePoints.CocpMain
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0222

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricToTangentPowerFreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_to_tangent_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0), GeomPF t x → TanPF t x p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free | exact GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free | (intros; apply GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GroupSchemeIntegralNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

theorem app_fst_sc_eq_zero {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V) (J : Ideal V) (U : X.Opens)
    {r : V} (hr : r ∈ J) :
    ((pullback.fst π (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).app U).hom (sc π U r) = 0 := by
  let j : Spec (CommRingCat.of (V ⧸ J)) ⟶ Spec (CommRingCat.of V) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let f := pullback.fst π j
  let g := pullback.snd π j
  have e1 := Scheme.Hom.appLE_comp_appLE f π ⊤ U (f ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e0 : ∀ e : ⊤ ≤ j ⁻¹ᵁ ⊤, (j.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = 0 := by
    intro e
    have a1 : j.appLE ⊤ ⊤ e = j.appTop := Scheme.Hom.appLE_eq_app (f := j) (U := ⊤)
    have a2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))
    have a3 : j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ J))).inv.hom (Ideal.Quotient.mk J r) :=
      (congrArg (fun q => q.hom r) a2).symm
    rw [a1, a3, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  have key : ∀ (w : pullback π j ⟶ Spec (CommRingCat.of V)) (_ : w = g ≫ j) (e : f ⁻¹ᵁ U ≤ w ⁻¹ᵁ ⊤),
      (w.appLE ⊤ (f ⁻¹ᵁ U) e).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r) = 0 := by
    rintro _ rfl e
    rw [← Scheme.Hom.appLE_comp_appLE g j ⊤ ⊤ (f ⁻¹ᵁ U) (fun _ _ => trivial) (fun _ _ => trivial),
      CommRingCat.comp_apply]
    exact (congrArg _ (e0 (fun _ _ => trivial))).trans (map_zero _)
  have h := key (f ≫ π) pullback.condition (fun _ _ => trivial)
  rw [← e1, CommRingCat.comp_apply] at h
  have e2 : f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U := Scheme.Hom.appLE_eq_app (f := f) (U := U)
  rw [e2] at h
  exact h

theorem semiAb_props : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsIntegral G.left ∧ ∀ W : G.left.Opens, IsAffineOpen W → IsNoetherianRing Γ(G.left, W) ∧ (sc G.hom W).FiniteType ∧ ∀ p : Ideal (𝓞 L), p.IsMaximal → ∀ a b : Γ(G.left, W), a * b ∈ p.map (sc G.hom W) → a ∈ p.map (sc G.hom W) ∨ b ∈ p.map (sc G.hom W) := by
  intro L _ _ G _ _ hG
  have := hG.smooth
  have := hG.geomConnected
  have hgi : GeometricallyIntegral G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  have : IsNoetherianRing (𝓞 L) := inferInstance
  have : IsLocallyNoetherian (Sp (𝓞 L)) := inferInstance
  have hI : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have hN : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  refine ⟨hI, fun W hW => ⟨?_, ?_, ?_⟩⟩
  · exact IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  · have h1 : (G.hom.appLE ⊤ W (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) G.hom inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (fun _ _ => trivial)
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv).2
    exact h1.comp h2
  · intro p hp a b hab
    letI : Field (𝓞 L ⧸ p) := Ideal.Quotient.field p
    let j : Spec (CommRingCat.of (𝓞 L ⧸ p)) ⟶ Sp (𝓞 L) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))
    have hY : IsIntegral (pullback G.hom j) :=
      GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom j)
    let f := pullback.fst G.hom j
    have hker : p.map (sc G.hom W) ≤ RingHom.ker (f.app W).hom :=
      Ideal.map_le_iff_le_comap.2 fun r hr => app_fst_sc_eq_zero G.hom p W hr
    have hz : (f.app W).hom a * (f.app W).hom b = 0 := by
      rw [← map_mul]
      exact hker hab
    have hab' : (f.app W).hom a = 0 ∨ (f.app W).hom b = 0 := by
      by_cases hne : Nonempty (f ⁻¹ᵁ W)
      · exact mul_eq_zero.1 hz
      · have hb : f ⁻¹ᵁ W = ⊥ := by
          ext x
          simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hne ⟨⟨x, hx⟩⟩
        have : Subsingleton Γ(pullback G.hom j, f ⁻¹ᵁ W) := by
          rw [hb]
          infer_instance
        exact Or.inl (Subsingleton.elim _ _)
    rcases hab' with h | h
    · exact Or.inl (DVR.mem_map_of_app_fst_eq_zero G.hom p hW a h)
    · exact Or.inr (DVR.mem_map_of_app_fst_eq_zero G.hom p hW b h)

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeIndexOfIntersection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem hodgeIndex_of_intersection :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Prov.HS := by
  intro hI hHS hBig hRes
  obtain ⟨g1, z1, z2, g6p, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Giv.hsLinks_of_moriwaki hHS hBig
  exact ⟨z1, z2, g1, g6p, GlobalTheory.T.big_line_implies_height_positivity hBig, GlobalTheory.T.hodge_index_implies_height_bound hHS, GlobalTheory.T.hilbert_samuel_G7s_of_statements hI hHS hRes,
    GlobalTheory.T.hilbert_samuel_G3_of_moriwaki hHS hBig, GlobalTheory.T.hilbert_samuel_G3Star_of_statements hI hHS hBig hRes⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelOfCurveBound
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.ModelNefness

theorem iSup_split {α I : Type} [CompleteLattice α] (f : I → α) (s₀ : I) :
    ⨆ s, f s = f s₀ ⊔ ⨆ s : {s // s ≠ s₀}, f s := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    by_cases h : s = s₀
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun s : {s // s ≠ s₀} => f s) ⟨s, h⟩)
  · exact sup_le (le_iSup f s₀) (iSup_le fun s => le_iSup f s.1)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isVBOn_iSup {E : Type} [AddCommGroup E] [Module Ω E] {I : Type} [Fintype I]
    (L : I → Lat ξ E) (T : Set (Cpt ξ)) (r : I → ℕ) (V : I → Submodule Ω E) (hV : iSupIndep V)
    (hL : ∀ s, (L s).IsVBOn T (r s) (V s)) :
    Lat.IsVBOn (ξ := ξ) (fun q => ⨆ s, L s q) T (∑ s, r s) (⨆ s, V s) := by
  classical
  intro p hp
  choose U hU b hb hfr using fun s => hL s p hp
  have hmem : ∀ (x : X) (s : Finset I), x ∈ s.inf U ↔ ∀ i ∈ s, x ∈ U i := by
    intro x s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.inf_insert, ih]
  let e : (Σ s, Fin (r s)) ≃ Fin (∑ s, r s) := Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma])
  let c : Fin (∑ s, r s) → E := fun i => b (e.symm i).1 (e.symm i).2
  have hsp : ∀ (A : Type) [Semiring A] [Module A E],
      Submodule.span A (Set.range c) = ⨆ s, Submodule.span A (Set.range (b s)) := by
    intro A _ _
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (le_iSup (fun s => Submodule.span A (Set.range (b s))) (e.symm i).1)
        (Submodule.subset_span ⟨_, rfl⟩)
    · refine iSup_le fun s => ?_
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨e ⟨s, i⟩, congrArg (fun x : Σ s, Fin (r s) => b x.1 x.2) (e.symm_apply_apply ⟨s, i⟩)⟩
  have hli : LinearIndependent Ω c := by
    have h1 : LinearIndependent Ω fun ji : Σ s, Fin (r s) => b ji.1 ji.2 := by
      refine linearIndependent_iUnion_finite (fun s => (hfr s p hp (hU s)).1) fun i t _ hi => ?_
      rw [hb i]
      refine (hV i).mono_right (iSup₂_le fun s hs => ?_)
      rw [hb s]
      exact le_iSup₂_of_le s (fun h => hi (h ▸ hs)) le_rfl
    exact h1.comp e.symm e.symm.injective
  refine ⟨Finset.univ.inf U, (hmem _ _).2 fun s _ => hU s, c, ?_, fun q hq hqU => ⟨hli, ?_⟩⟩
  · rw [hsp Ω]
    exact iSup_congr hb
  · rw [hsp (regAt ξ q)]
    exact iSup_congr fun s => (hfr s q hq ((hmem _ _).1 hqU s (Finset.mem_univ s))).2

theorem unitAt_of_isUnit {q : Cpt ξ} {a : regAt ξ q} (h : IsUnit a) : unitAt ξ q (a : Ω) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨fun h0 => u.ne_zero (Subtype.ext h0), u.1.2, ?_⟩
  have : ((u : regAt ξ q) : Ω)⁻¹ = (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q) : Ω) := by
    exact inv_eq_of_mul_eq_one_right (congrArg Subtype.val u.mul_inv)
  rw [this]
  exact (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q)).2

theorem unitAt_int_of_fibre [CharZero Ω] {p : ℕ} (hp : p.Prime) (q : Cpt ξ) (hq : InFibre ξ p q) {d : ℤ}
    (hd : ¬ (p : ℤ) ∣ d) : unitAt ξ q (d : Ω) := by
  haveI := EigSplit.isLocalRing_regAt q
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd).2 hd
  have hP : ¬ IsUnit ((p : ℕ) : regAt ξ q) := fun h => hq (by simpa using unitAt_of_isUnit h)
  have h1 : ((a : regAt ξ q) * (p : regAt ξ q)) + (b : regAt ξ q) * (d : regAt ξ q) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → regAt ξ q) hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hP
  · have e : ((d : regAt ξ q) : Ω) = (d : Ω) := map_intCast (regAt ξ q).subtype d
    rw [← e]
    exact unitAt_of_isUnit (isUnit_of_mul_isUnit_right (x := (b : regAt ξ q)) (by rwa [mul_comm] at h ⊢))

theorem charZero_of_isArithVar {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {d : ℕ}
    (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  obtain ⟨-, -, hh, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have : mConeMap y (MvPolynomial.C (n : ℤ)) = MvPolynomial.C (n : Ω) := by
      simpa using (mConeMap y).commutes (n : ℤ)
    simpa [hn] using this
  rw [show (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) = ⊥ from hh] at h1
  simpa using h1

open Module in

theorem flag_at (E : Type) [Field E] [NumberField E] [CharZero Ω] (hg : IsCptGen ξ)
    {K k : Type} [Field K] [Field k] [Algebra k K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z)
    (G : Over X) [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom) (act : OAct (𝓞 E) G)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V)
    (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz)
    (r : 𝓞 E →+* Module.End Ω V) (rz : 𝓞 E →+* Module.End K Vz) (hr : M.IsActOf act.act r)
    (hrz : Mz.IsActOf act.act rz) (I : Type) [Fintype I] (σ : I → (𝓞 E →+* Ω)) (χ : I → (𝓞 E →+* k))
    (hσ : Function.Injective σ) (hcard : Fintype.card I = finrank ℚ E) (hχ : IsSplit χ)
    (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ))
    (hz : (⟨centre z, h₀⟩ : Cpt ξ) ∈ S) (hS : ∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S)
    (hreg : ∀ q ∈ S, ∀ s a, σ s a ∈ regAt ξ q) (hdisc : ∀ q ∈ S, unitAt ξ q ((discr E : ℤ) : Ω))
    (hval : ∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a)))
    (s₀ : I) {n : ℕ} (b : Fin n → V) (hb : LinearIndependent Ω b)
    (hspan : Submodule.span Ω (Set.range b) = eigSp r (σ s₀)) (hfl : (M.eigLat r (σ s₀)).IsFlagVBOn S b) :
    ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W n = eigSp rz ((algebraMap k K).comp (χ s₀)) ∧
      ∀ s : Fin n, Y.IsDeg ((M.eigLat r (σ s₀)).gr b s)
        (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  classical
  have hvb : M.lat.IsVBOn S (finrank Ω V) ⊤ := fun p _ => by
    obtain ⟨U, hU, c, hc, hf⟩ := (GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ G V M hg hsm).1 p trivial
    exact ⟨U, hU, c, hc, fun q _ hq => hf q trivial hq⟩
  obtain ⟨hE, hsum⟩ := EigSplit.isVBOn_eigSp X Ω ξ V E r M.lat S _ I σ hg hσ hcard hvb
    (fun p _ a e he => LieStable.lat_stable X Ω ξ G V M _ act r hr p a e he) hreg hdisc
  have hint := GlobalTheory.T.eigenspace_decomposition_internal Ω V E r I σ hσ hcard
  have hind := hint.submodule_iSupIndep
  let U' : Submodule Ω V := ⨆ s : {s // s ≠ s₀}, eigSp r (σ s)
  let L' : Lat ξ V := fun q => ⨆ s : {s // s ≠ s₀}, M.eigLat r (σ s) q
  have hL' : L'.IsVBOn S (∑ s : {s // s ≠ s₀}, finrank Ω (eigSp r (σ s))) U' :=
    isVBOn_iSup (fun s : {s // s ≠ s₀} => M.eigLat r (σ s)) S _ (fun s => eigSp r (σ s))
      (hind.comp Subtype.val_injective) fun s => hE s
  have hcompl : IsCompl (Submodule.span Ω (Set.range b)) U' := by
    rw [hspan]
    refine ⟨(hind s₀).mono_right (iSup_le fun s => le_iSup₂_of_le s.1 s.2 le_rfl), ?_⟩
    rw [codisjoint_iff, ← iSup_split (fun s => eigSp r (σ s)) s₀]
    exact hint.submodule_iSup_eq_top
  have hlat : ∀ q ∈ S, M.lat q = M.eigLat r (σ s₀) q ⊔ L' q := fun q hq =>
    (hsum q hq).trans (iSup_split (fun s => M.eigLat r (σ s) q) s₀)
  obtain ⟨W, hW0, hWn, hdeg⟩ := GlobalTheory.T.curve_lie_lattice_degree X Ω ξ K C z Y G V M Vz Mz h₀ h S (M.eigLat r (σ s₀)) L' n _ b U'
    hg hsm hz hS hb hfl hL' hcompl hlat
  refine ⟨W, hW0, ?_, hdeg⟩
  rw [hWn]
  exact GlobalTheory.T.curve_lie_eigen_decomposition X Ω ξ k K z G V M Vz Mz h₀ (𝓞 E) I act.act r rz σ χ hg hsm act.hom hr hrz hχ hval
    (hsum _ hz) s₀

end GlobalTheory.CompanionTheory.Ar.Conj.ModelNefness

namespace GlobalTheory.CompanionTheory.Ar.Conj

open ModelNefness GlobalTheory.CompanionTheory.Ar.Top in

theorem m2Model_of_m2Curve : CurveSemiAbelianConjecture → RootLineDeRhamModel := by
  intro hC Ψ _ N M j p E _ _ _ H D hp hp2 hj hjN mu hdom hthr Wi hW
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hprime, hPW, hchar, hdim⟩ := hW
  haveI : CharZero M.Ω := charZero_of_isArithVar M.arith
  obtain ⟨K, _, _, _, w, hwW, hbir, hwk⟩ := GlobalTheory.T.function_field_model_exists M.K M.ι Wi p hprime hchar hdim
  obtain ⟨C, hFF, hne, hv⟩ := GlobalTheory.T.function_field_curve_exists (ZMod p) K
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  obtain ⟨z, Y, h₀, h, hco, hfib⟩ := GlobalTheory.T.curve_through_coordinates D.X M.Ω D.ξ M.K M.ι M.y D.tie K C w
    (by rw [hwW]; exact hPW) hwk
  obtain ⟨hz, hi⟩ := hfib p (CharP.cast_eq_zero K p)
  have hg : IsCptGen D.ξ := D.tie.gen
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom D.X M.Ω D.ξ K z h₀ hg
  let σ' : Ψ ⊕ Ψ → (𝓞 E →+* regAt D.ξ ⟨centre z, h₀⟩) := fun s => (D.σ s).codRestrict _ (D.reg _ hz s)
  have hσ' : Function.Injective σ' := fun s s' e => D.σ_inj (RingHom.ext fun a =>
    congrArg Subtype.val (RingHom.congr_fun e a))
  have hcard : Fintype.card (Ψ ⊕ Ψ) = Module.finrank ℚ E := by
    rw [Fintype.card_sum, ← D.card]; ring
  obtain ⟨χ, hχ, hχv⟩ := GlobalTheory.T.split_characters_unramified E (regAt D.ξ ⟨centre z, h₀⟩) K (Ψ ⊕ Ψ) p σ' φ hσ' hcard D.unram
  have hval : ∀ s a, ValAt D.ξ z (D.σ s a) (algebraMap (algebraicClosure (ZMod p) K) K (χ s a)) := fun s a =>
    (hφ _ _).2 ⟨D.reg _ hz s a, (hχv s a).symm⟩
  have hconj : ∀ τ a, χ (Sum.inr τ) a = χ (Sum.inl τ) (H.bar a) := fun τ a => Subtype.ext (by
    rw [hχv, hχv]
    exact congrArg φ (Subtype.ext (D.conj τ a)))
  have hconst : ∀ i (c : algebraicClosure (ZMod p) K), C.v i (algebraMap _ K c) ≤ 1 := fun i c =>
    hv i _ (mem_algebraicClosure_iff.1 c.2)
  obtain ⟨Vz, _, _, ⟨Mz⟩⟩ := lieModel_exists D.X D.t.G K z
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  haveI : FiniteDimensional K Vz := (GlobalTheory.T.lie_model_finite_projective D.X D.t.G K z Vz Mz).1
  obtain ⟨rz, hrz, -⟩ := lieModel_exists_unique_act D.X D.t.G K z Vz Mz (𝓞 E) D.t.act.act D.t.act.hom
    D.t.act.one D.t.act.mul D.t.act.add
  have hreg : ∀ q ∈ {q | InFibre D.ξ p q}, ∀ s a, D.σ s a ∈ regAt D.ξ q := fun q hq s a => D.reg q hq s a
  have hdisc : ∀ q ∈ {q | InFibre D.ξ p q}, unitAt D.ξ q ((NumberField.discr E : ℤ) : M.Ω) := fun q hq =>
    unitAt_int_of_fibre hp q hq D.unram
  choose Wf hW0 hWj hdegW using fun τ => flag_at E hg C z Y D.t.G D.t.semi.smooth D.t.act D.V D.L Vz Mz D.r rz
    D.act hrz (Ψ ⊕ Ψ) D.σ χ D.σ_inj hcard hχ h₀ h {q | InFibre D.ξ p q} hz hi hreg hdisc hval (Sum.inl τ)
    (D.b₁ τ) (D.ind₁ τ).1 (D.ind₁ τ).2 (D.flag₁ τ)
  choose Lf hL0 hLq hdegL using fun τ => flag_at E hg C z Y D.t.G D.t.semi.smooth D.t.act D.V D.L Vz Mz D.r rz
    D.act hrz (Ψ ⊕ Ψ) D.σ χ D.σ_inj hcard hχ h₀ h {q | InFibre D.ξ p q} hz hi hreg hdisc hval (Sum.inr τ)
    (D.b₂ τ) (D.ind₂ τ).1 (D.ind₂ τ).2 (D.flag₂ τ)
  have hxdeg : ∀ r, geoNum 1 Wi (fun _ => M.xdeg r) = coordDeg C w (M.xdeg r) := fun r => by
    rw [← hwW]
    exact GlobalTheory.T.function_field_degree_eq M.K M.ι p K C w (M.xdeg r) hFF hbir hwk
  let x : Ψ × Fin N → ℝ := fun r => (geoNum 1 Wi (fun _ => M.xdeg r) : ℝ)
  let wd : Ψ → ℕ → ℝ := fun τ i => (subDeg C (Y.lieLat Mz) (Wf τ i) : ℝ)
  let ld : Ψ → ℕ → ℝ := fun τ i => (subDeg C (Y.lieLat Mz) (Lf τ i) : ℝ)
  have hx1 : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = wd τ (i + 1) - wd τ i := by
    intro τ i hij
    obtain ⟨e₀, hdo⟩ := D.deg₁ τ i hij
    have h1 := GlobalTheory.T.curve_lattice_degree_formula D.X M.Ω D.ξ K C z Y M.K M.ι M.y w _ {q | InFibre D.ξ p q} _ e₀ h₀ h D.tie hco hz hi hdo
    have h2 := GlobalTheory.T.curve_degree_unique D.X M.Ω D.ξ K C z Y _ _ _ hg h1 (hdegW τ ⟨i, hij⟩)
    simp only [x, wd, hxdeg, h2]
    push_cast
    rfl
  have hx2 : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(ld τ (N - 1 - i + 1) - ld τ (N - 1 - i)) := by
    intro τ i hij
    have hlt : N - 1 - (i : ℕ) < N - j := by have := i.2; omega
    obtain ⟨e₀, hdo⟩ := D.deg₂ τ i hlt hij
    have h1 := GlobalTheory.T.curve_lattice_degree_formula D.X M.Ω D.ξ K C z Y M.K M.ι M.y w _ {q | InFibre D.ξ p q} _ e₀ h₀ h D.tie hco hz hi hdo
    have h2 := GlobalTheory.T.curve_degree_unique D.X M.Ω D.ξ K C z Y _ _ _ hg h1 (hdegL τ ⟨N - 1 - i, hlt⟩)
    have h3 : coordDeg C w (-M.xdeg (τ, i)) = -coordDeg C w (M.xdeg (τ, i)) := by
      simp [coordDeg]
    rw [h3] at h2
    have h4 : coordDeg C w (M.xdeg (τ, i)) = -(subDeg C (Y.lieLat Mz) (Lf τ (N - 1 - i + 1)) -
        subDeg C (Y.lieLat Mz) (Lf τ (N - 1 - i))) := by
      rw [← neg_eq_iff_eq_neg]; exact h2
    simp only [x, ld, hxdeg, h4]
    push_cast
    rfl
  obtain ⟨hgap, heq⟩ := GlobalTheory.T.nef_threshold_gap_condition Ψ N j p mu x wd ld hp2 hj hjN hdom hthr hx1 hx2
  have hfin := hC E H D.X D.t D.pow (algebraicClosure (ZMod p) K) K p hp2 C z Y hne hconst
    (fun i => D.fib ⟨_, h i⟩ (hi i)) Vz Mz rz hrz Ψ χ hχ hconj j (N - j) _ Wf Lf hj (by omega) hW0 hL0 hWj hLq hgap
  have hfin' : 0 ≤ ∑ r : Ψ × Fin N, -mu r.1 r.2 * x r := heq ▸ hfin
  have hcd : M.curveDeg mu 0 Wi = ∑ r : Ψ × Fin N, -mu r.1 r.2 * x r := by
    unfold RootModel.curveDeg
    rw [Fintype.sum_option]
    simp only [RootModel.coef, RootModel.line, M.x_deg, zero_div, zero_mul, zero_add, x]
  rw [hcd]
  exact hfin'

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveRootHodgeCptStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_root_hodge_cpt : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ) (ζ : Ωˣ), p ∈ S → 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → IsPrimitiveRoot ζ (p ^ 𝔐.R p) → ∃ (τ : (Fin (D.p + D.q) → 𝓞 E) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G)) (ew : (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) → Ωˣ) (e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p)), (∀ x x', τ (x + x') = τ x * τ x') ∧ (∀ (a : 𝓞 E) x, τ (a • x) = τ x ≫ 𝔐.t.act.act a) ∧ (∀ g, g ^ (p ^ 𝔐.R p) = 1 ↔ ∃ x, τ x = g) ∧ GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ (p ^ 𝔐.R p) ew ∧ (∀ x x', ew (τ x) (τ x') = ζ ^ (e x x').val) ∧ (∀ x, e x x = 0) ∧ (∀ (a : 𝓞 E) x x', e (a • x) x' = e x (RingOfIntegers.mapRingEquiv (HT.cmConj E) a • x')) ∧ (∀ φ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p), ∃ x, e x = φ) ∧ ∀ x, e x = 0 → ∃ x', x = (p ^ 𝔐.R p) • x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HF.generic_torsion | exact GlobalTheory.CompanionTheory.Ar.HF.generic_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.HF.generic_torsion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameFinalStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_generic_frame_final : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → (letI := io.toAlgebra; Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.ptY_eq_gen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentPowerFreeConjInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tangent_power_free_conj_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), TanPF t x p → ConjInj g.B p := by
  first | exact @PositivityTheory.HtPt.Cocp.tanpf_inj | exact PositivityTheory.HtPt.Cocp.tanpf_inj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLieModelLiftStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_lie_model_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (v : epsOver T.V T.V ⟶ G.G), IsTan v → ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.exists_val_of_isTan <;> assumption)
end

