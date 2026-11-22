import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0302
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0291
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0212
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0298
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0215
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0303
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeBound
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamLat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isLocalRing_regAt (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

theorem coordLat_locFree (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (hT : CoordTie ℤ ξ (mseg y)) (A : Type)
    [CommRing A] [Algebra A Ω] (hA : HasConstants ℤ A y) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (Vg : Submodule Ω V) (b : Fin r → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = Vg)
    (hVB : L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt ξ q} r Vg) (c : ∀ k, J k) (hc : mseg y c ≠ 0) :
    LocFree (chartRing O (mseg y) c) r (coordLat O y L b c) ∧ ∀ g ∈ chartRing O (mseg y) c, ∀ e : Fin r → Ω,
      (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → g ≠ 0 → g⁻¹ ∈ regAt ξ q →
        Fintype.linearCombination Ω b e ∈ L q) → ∃ n : ℕ, g ^ n • e ∈ coordLat O y L b c := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.dvr_localization_constants X Ω ξ K J y hT A hA m O c hc
  let Q : Type := {q : Cpt ξ // InChart ξ (mseg y) c q ∧ ∀ o : O, algebraMap O Ω o ∈ regAt ξ q}
  let Λ : Q → AddSubgroup (Fin r → Ω) := fun q =>
    (L q.1).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom
  have hcoord : coordLat O y L b c = ⨅ q, Λ q := by
    ext e
    simp only [coordLat, AddSubgroup.mem_iInf, Subtype.forall, Λ, Q]
    exact ⟨fun h q hq => h q hq.1 hq.2, fun h q h1 h2 => h q ⟨h1, h2⟩⟩
  have hinj : Function.Injective (Fintype.linearCombination Ω b) :=
    hli.fintypeLinearCombination_injective
  have hfr : ∀ q : Q, ∃ g ∈ chartRing O (mseg y) c, g ≠ 0 ∧ g⁻¹ ∈ regAt ξ q.1 ∧
      ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q' : Q, g⁻¹ ∈ regAt ξ q'.1 → ∀ e, e ∈ Λ q' ↔
        ∃ a : Fin r → Ω, (∀ i, a i ∈ regAt ξ q'.1) ∧ e = ∑ i, a i • f i := by
    intro q
    obtain ⟨U, hU, f, hfs, hf⟩ := hVB q.1 q.2.2
    obtain ⟨g, hg, hgu, hgU⟩ := h4 q.1 q.2.1 q.2.2 U hU
    have hmem : ∀ i, ∃ f' : Fin r → Ω, Fintype.linearCombination Ω b f' = f i := by
      intro i
      have : f i ∈ Submodule.span Ω (Set.range b) := by
        rw [hsp, ← hfs]; exact Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
      exact ⟨a, by rw [Fintype.linearCombination_apply]; exact ha⟩
    choose f' hf' using hmem
    refine ⟨g, hg, hgu.1, hgu.2.2, f', ?_, fun q' hq' e => ?_⟩
    · have hl := (hf q.1 q.2.2 hU).1
      have : (Fintype.linearCombination Ω b) ∘ f' = f := funext hf'
      rw [← this] at hl
      exact hl.of_comp _
    · have hu : unitAt ξ q'.1 g := ⟨hgu.1, h1 g hg q'.1 q'.2.1 q'.2.2, hq'⟩
      have hq'U := hgU q'.1 q'.2.1 q'.2.2 hu
      have hfrm := (hf q'.1 q'.2.2 hq'U).2
      show Fintype.linearCombination Ω b e ∈ L q'.1 ↔ _
      rw [hfrm]
      constructor
      · intro he
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ q'.1)).1 he
        refine ⟨fun i => (a i : Ω), fun i => (a i).2, hinj ?_⟩
        rw [← ha, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hf']
        rfl
      · rintro ⟨a, ha, rfl⟩
        refine (Submodule.mem_span_range_iff_exists_fun (regAt ξ q'.1)).2 ⟨fun i => ⟨a i, ha i⟩, ?_⟩
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hf']
        rfl
  have key := GlobalTheory.T.regular_lattice_local_free (chartRing O (mseg y) c) Q (fun q => regAt ξ q.1) r Λ (fun q => isLocalRing_regAt q.1)
    (fun q a ha => h1 a ha q.1 q.2.1 q.2.2)
    (fun P hP => by
      obtain ⟨q, hq1, hq2, hq⟩ := h2 P hP
      refine ⟨⟨q, hq1, hq2⟩, fun s => ?_⟩
      rw [hq s]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h1 _ s.2 q hq1 hq2, h.2⟩⟩)
    (fun q a ha => by
      obtain ⟨s, hs, hu, hsa⟩ := h3 q.1 q.2.1 q.2.2 a ha
      exact ⟨s, hs, hu.1, hu.2.2, hsa⟩)
    hfr
  rw [hcoord]
  refine ⟨key.1, fun g hg e he => key.2 g hg e fun q h h' => ?_⟩
  exact he q.1 q.2.1 q.2.2 h h'

theorem coordLat_family (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (hT : CoordTie ℤ ξ (mseg y)) (A : Type)
    [CommRing A] [Algebra A Ω] (hA : HasConstants ℤ A y) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (Vg : Submodule Ω V) (b : Fin r → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = Vg)
    (hVB : L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt ξ q} r Vg) :
    IsLatFamily O y (coordLat O y L b) := by
  have key := coordLat_locFree X Ω ξ K J y hT A hA m O V L r Vg b hli hsp hVB
  refine ⟨fun s hs a ha v hv => (key s hs).1.1 a ha v hv, fun s t hs ht v hv => ?_⟩
  have hg : mseg y s / mseg y t ∈ chartRing O (mseg y) t := Algebra.subset_adjoin ⟨s, rfl⟩
  refine (key t ht).2 _ hg v fun q hq hO hg0 hgi => ?_
  have hqs : InChart ξ (mseg y) s q := by
    refine ⟨hs, fun c' => ?_⟩
    have e : mseg y c' / mseg y s = mseg y c' / mseg y t * (mseg y s / mseg y t)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hq.2 c') hgi
  have := (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hqs) hO)
  exact this

theorem coordLat_mono {O : Type} [CommRing O] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V] {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V)
    (c : ∀ k, J k) (h : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → L q ≤ L' q) :
    coordLat O y L b c ≤ coordLat O y L' b c := by
  intro v hv
  refine AddSubgroup.mem_iInf.2 fun q => AddSubgroup.mem_iInf.2 fun hq => AddSubgroup.mem_iInf.2 fun hO => ?_
  exact h q hO (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hq) hO)

theorem coordLat_le_divLat {O : Type} [CommRing O] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V] {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V)
    (c : ∀ k, J k) (a : Ω) (h : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ e ∈ L' q, a • e ∈ L q) :
    coordLat O y L' b c ≤ divLat a (coordLat O y L b c) := by
  intro v hv
  show a • v ∈ coordLat O y L b c
  refine AddSubgroup.mem_iInf.2 fun q => AddSubgroup.mem_iInf.2 fun hq => AddSubgroup.mem_iInf.2 fun hO => ?_
  have := h q hO _ (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hq) hO)
  show Fintype.linearCombination Ω b (a • v) ∈ L q
  rw [map_smul]
  exact this

theorem mem_dotDual' {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ} (L : AddSubgroup (Fin n → Ω))
    (v : Fin n → Ω) : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf]
  rfl

theorem dotDual_anti {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ} {L L' : AddSubgroup (Fin n → Ω)}
    (h : L ≤ L') : dotDual R L' ≤ dotDual R L := fun v hv =>
  (mem_dotDual' R L v).2 fun l hl => (mem_dotDual' R L' v).1 hv l (h hl)

theorem dotDual_le_divLat {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ}
    {L L' : AddSubgroup (Fin n → Ω)} (a : Ω) (h : L' ≤ divLat a L) : dotDual R L ≤ divLat a (dotDual R L') := by
  intro v hv
  show a • v ∈ dotDual R L'
  refine (mem_dotDual' R L' _).2 fun l hl => ?_
  have h2 := (mem_dotDual' R L v).1 hv _ (show a • l ∈ L from h hl)
  rwa [dotProduct_smul, ← smul_dotProduct]

theorem unit_of_place {A : Type} [CommRing A] [Algebra A Ω] {m : Ideal A} [m.IsPrime] {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] {p : ℕ} (hpm : (p : A) ∈ m) (hp : p.Prime) {q : Cpt ξ}
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) : q ∈ overPrime ξ p := by
  intro r hr hrp hf
  have hco : IsCoprime (r : ℤ) (p : ℤ) := by
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hr hp).2 hrp)
  obtain ⟨a, b, hab⟩ := hco
  have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hpm
    simpa using this
  have hrO : IsUnit (r : O) := by
    by_contra hn
    have hr' : (r : O) ∈ IsLocalRing.maximalIdeal O := hn
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have e : (1 : O) = (a : O) * (r : O) + (b : O) * (p : O) := by
        have := congrArg (Int.cast : ℤ → O) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hr') (Ideal.mul_mem_left _ _ hpO)
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal O).ne_top this
  obtain ⟨u, hu⟩ := hrO.exists_right_inv
  have hu' : (r : Ω) * algebraMap O Ω u = 1 := by
    have := congrArg (algebraMap O Ω) hu
    simpa using this
  have hr0 : (r : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hu'
  refine hf ⟨hr0, natCast_mem _ r, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hu']
  exact hO u

theorem lat_main : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ t : CMType H ⊕ CMType H, IsLatFamily O y (fun c' => coordLat O y (𝔐.dR t) (b t) c') ∧ IsLatFamily O y (fun c' => coordLat O y (𝔐.HT p t) (b t) c') ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ coordLat O y (𝔐.dR t) (b t) c' ≤ coordLat O y (𝔐.HT p t) (b t) c' ∧ coordLat O y (𝔐.HT p t) (b t) c' ≤ divLat (algebraMap O Ω w) (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c') ≤ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ≤ divLat (algebraMap O Ω w) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hvar hpq p _ hpS hfree hp2 hdisc b hb A _ _ _ m _ hpm O _ _ _ _
    _ _ _ w hw t
  have hpp : p.Prime := Fact.out
  have hG : Nonempty (GenTors 𝔐 p) := GlobalTheory.T.arith_variety_hodge_prime_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar hpq p hpS hfree hp2 hdisc
  obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hpq hfree
  obtain ⟨-, -, -, hcon, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar A
  have hE := GlobalTheory.T.generic_torsion_unramified_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hG hdisc
  obtain ⟨hV1, hV2⟩ := GlobalTheory.T.cm_flag_unramified_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hdisc hE t
  have hT : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hO : ∀ q : Cpt 𝔐.ξ, (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → q ∈ overPrime 𝔐.ξ p :=
    fun q h => unit_of_place (A := A) (m := m) (O := O) hpm hpp h
  have hres : ∀ (L : Lat 𝔐.ξ 𝔐.Li), L.IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) →
      L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q} (labelRk D t) (𝔐.Vgen t) := by
    intro L hL q hq
    obtain ⟨U, hU, f, hf, hfr⟩ := hL q (hO q hq)
    exact ⟨U, hU, f, hf, fun q' hq' hq'U => hfr q' (hO q' hq') hq'U⟩
  have hdF := coordLat_family _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.dR t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV1)
  have hhF := coordLat_family _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.HT p t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV2)
  have hdL : ∀ c', mseg y c' ≠ 0 → LocFree (chartRing O (mseg y) c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') :=
    fun c' hc' => (coordLat_locFree _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.dR t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV1) c' hc').1
  have hhL : ∀ c', mseg y c' ≠ 0 → LocFree (chartRing O (mseg y) c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') :=
    fun c' hc' => (coordLat_locFree _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.HT p t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV2) c' hc').1
  obtain ⟨hdD, hdDL⟩ := GlobalTheory.T.dot_dual_lattice_family O Ω K J y _ _ hdF hdL
  obtain ⟨hhD, hhDL⟩ := GlobalTheory.T.dot_dual_lattice_family O Ω K J y _ _ hhF hhL
  have hpt : ∀ q : Cpt 𝔐.ξ, (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) →
      𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, algebraMap O Ω w • e ∈ 𝔐.dR t q := by
    intro q hq
    by_cases hf : InFibre 𝔐.ξ p q
    · exact GlobalTheory.T.cp_ratio_unramified_odd_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hp2 hdisc κ _ hκ hw hS q hf (hq w) t
    · have hall : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q := fun r hr => by
        by_cases hrp : r = p
        · exact hrp ▸ hf
        · exact hO q hq r hr hrp
      rw [hE t q hall]
      exact ⟨le_rfl, fun e he => (𝔐.dR t q).smul_mem (⟨_, hq w⟩ : regAt 𝔐.ξ q) he⟩
  refine ⟨hdF, hhF, hdD, hhD, fun c' hc' => ⟨hdL c' hc', hhL c' hc', hdDL c' hc', hhDL c' hc', ?_, ?_, ?_, ?_⟩⟩
  · exact coordLat_mono y (b t) c' fun q hq => (hpt q hq).1
  · exact coordLat_le_divLat y (b t) c' _ fun q hq => (hpt q hq).2
  · exact dotDual_anti _ (coordLat_mono y (b t) c' fun q hq => (hpt q hq).1)
  · exact dotDual_le_divLat _ _ (coordLat_le_divLat y (b t) c' _ fun q hq => (hpt q hq).2)

end GlobalTheory.CompanionTheory.Ar.Num.FamLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionLimitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_chart_log_growth_bounds : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → ChartBdd Dc (corrW Hd U) ∧ ∀ a, ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, ∃ ε > (0 : ℝ), ∃ C : ℝ, ∀ t ∈ offBd Dc a, ‖t - t₀‖ < ε → U ((Dc.chart a).γ t) ≤ C * Real.log ((Dc.chart a).logR t) ∧ |phMu Hd ((Dc.chart a).γ t)| ≤ C * Real.log ((Dc.chart a).logR t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd.corr_bdd | exact GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd.corr_bdd | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd.corr_bdd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFunctionCompareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frame_function_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (ξ' : Sp Z.Ω ⟶ X') (W' W : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (F : (Sp ℂ ⟶ X') → ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → W ≤ W' → (∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' → y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w) → (∀ p : Cpt ξ', p.1 ∈ W → ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1) → ∀ (x : Sp ℂ ⟶ X') (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap σ → ∃ t : Z.Ω, ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' σ ξ' W F t x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution | exact GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBoundStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_chart_exists_seqHyp_gram_congr_mod_pow : ∀ (o Ω Li : Type) [CommRing o] [Field Ω] [CharZero Ω] [Algebra o Ω] (R : Subalgebra o Ω) [IsNoetherianRing R] [IsFractionRing R Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (_ : ∀ x, c (c x) = x) (p Rr N r s m : ℕ) [Fact p.Prime] [AddCommGroup Li] [Module Ω Li] (D : HT.HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li), (∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* Ω) (i₀ : Module.Dual R (D.omHT (σ.comp c.toRingHom)) →ₗ[R] (Fin N → R)), D.ExactMod σ m i₀ → D.IsDualMap σ 1 m i₀ → Module.Projective R (D.omHT σ) → ∀ (v : Fin r → Li) (v' : Fin s → Li), LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω v' → Submodule.span Ω (Set.range v') = HT.eigSp ρ (σ.comp c.toRingHom) → ∀ (W : AddSubgroup (Fin r → Ω)) (W' : AddSubgroup (Fin s → Ω)), (∀ a, a ∈ W ↔ ∀ u ∈ D.om', u (∑ k, a k • v k) ∈ R) → (∀ a, a ∈ W' ↔ ∀ u ∈ D.om', u (∑ k, a k • v' k) ∈ R) → ∀ w : Ω, w ∈ R → (∃ u ∈ R, (p : Ω) ^ m = w * u) → ∃ i : (Fin r → Ω) →ₗ[Ω] (Fin N → Ω), SeqHyp R w W (dotDual R W') i (Fintype.linearCombination Ω fun (n : Fin N) (k : Fin s) => D.h (Pi.single n 1) (v' k)) ∧ ∀ a ∈ W, ∀ j, ∃ z ∈ R, ∑ l, i a l * D.gram σ 1 l j = D.h (Pi.single j 1) (∑ k, a k • v k) + (p : Ω) ^ m * z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrimitiveRootOfLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeExists

theorem coordTie_reindex {o : Type} [CommRing o] {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra o Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' → κ)
    (he : Function.Surjective e) (x' : κ' → Ω) (hx : ∀ c, x' c = x (e c)) : CoordTie o ξ x' := by
  obtain rfl : x' = fun c => x (e c) := funext hx
  have hc : ∀ c p, InChart ξ (fun c => x (e c)) c p ↔ InChart ξ x (e c) p := fun c p =>
    and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (e c) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    obtain ⟨c, rfl⟩ := he c
    exact ⟨c, (hc c p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      he.range_comp fun j => x j / x (e c)
    simpa only [hc, this] using h.ring (e c) h0 a

theorem exists_lift_torsion {S S' Z : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (b : Z ⟶ S') (a : Z ⟶ S) (hab : a = b ≫ f) (n : ℕ)
    (g : Over.mk a ⟶ G) (hg : g ^ n = 1) : ∃ g' : Over.mk b ⟶ G', g'.left ≫ φ = g.left ∧ g' ^ n = 1 := by
  subst hab
  let P : (Over.mk b ⟶ G') → (Over.mk (b ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this])
  have hP : ∀ x, (P x).left = x.left ≫ φ := fun _ => rfl
  let Φ : (Over.mk b ⟶ G') →* (Over.mk (b ≫ f) ⟶ G) := MonoidHom.mk' P fun x y =>
    Over.OverMorphism.ext ((hP _).trans (h.2 (Over.mk b) x y (P x) (P y) rfl rfl).symm)
  have hinj : Function.Injective Φ := fun x y hxy => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg CommaMorphism.left hxy) ((Over.w x).trans (Over.w y).symm))
  let g' : Over.mk b ⟶ G' := Over.homMk (h.1.lift g.left b (Over.w g)) (h.1.lift_snd _ _ _)
  have hg' : g'.left ≫ φ = g.left := h.1.lift_fst _ _ _
  refine ⟨g', hg', hinj ?_⟩
  have : Φ g' = g := Over.OverMorphism.ext hg'
  rw [map_pow, this, hg, map_one]

theorem fullTorsion_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ S'}
    {N n : ℕ} (hn : n ∣ N) (ht : FullTorsion G' ξ N) : FullTorsion G (ξ ≫ f) n := by
  intro k _ i g hg
  obtain ⟨g', e, hg'⟩ := exists_lift_torsion h (spMap i ≫ ξ) _ (Category.assoc _ _ _).symm n g hg
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, hx⟩ := ht k i g' (by rw [pow_mul, hg', one_pow])
  refine ⟨Over.homMk (x.left ≫ φ) ?_, ?_⟩
  · have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this]
  · rw [← e, hx]
    exact Category.assoc _ _ _

theorem finite_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} (hξ : IsCptGen ξ) (f : X ⟶ Y) [IsFinite f] {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : i.Finite := by
  have h1 : LocallyQuasiFinite (Spec.map (Scheme.stalkClosedPointTo ξ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).2
      (.of_finite (RingHom.Finite.of_surjective _ hξ.bij.2))
  have h2 : LocallyQuasiFinite ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    infer_instance
  have h3 : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) := by
    rw [← h]
    infer_instance
  have h4 : i.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite) (φ := CommRingCat.ofHom i)).1
      (LocallyQuasiFinite.of_comp _ ξ₀)
  algebraize [i]
  exact .of_quasiFinite

theorem genPt_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} {f : X ⟶ Y} {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : f (GlobalTheory.CompanionTheory.Ar.genPt ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ := by
  refine (Scheme.Hom.comp_apply ξ f _).symm.trans ?_
  rw [show ξ ≫ f = _ from h]
  exact (Scheme.Hom.comp_apply _ ξ₀ _).trans
    (congrArg ξ₀ (Subsingleton.elim (α := PrimeSpectrum Ω₀) _ _))

theorem isPrimitiveRoot_of_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {X : Scheme.{0}} {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} (hN : 0 < N) {z : Ωˣ}
    {ev : D.La → (Over.mk ξ ⟶ t.G)} (h : XR.IsFullLevelAt D t ξ N z ev) : IsPrimitiveRoot (z : Ω) N := by
  obtain ⟨I, hI, -⟩ := h (AlgebraicClosure Ω) (algebraMap Ω _)
  refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap Ω (AlgebraicClosure Ω)) ?_ (RingHom.injective _)
  rw [← hI]
  exact IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim N hN)

theorem exists_hodgeCpt_flag : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (R : ℕ → ℕ) (e₀ : Y.X), e₀ ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, 4 ≤ R p) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), 𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt 𝔐.ξ) = e₀ ∧ 𝔐.R = R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ Fl.RootLines xdeg e ∧ ∀ s, (𝔐.dR s).IsFlagVBOn Set.univ (Fl.b s) := by
  intro hW E _ _ _ H D l Xo c Y S R e₀ he hS hd hR
  have hN : 0 < ∏ p ∈ S, p ^ R p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  obtain ⟨Ω, _, _, n, x, M, f, y₀, t, m, z, ev, hnorm, hfin, hf, hy, hlev, htor, -⟩ :=
    GlobalTheory.T.LevelCoverSt_holds E H D l Xo c Y e₀ he _ hN
  have hz := isPrimitiveRoot_of_level hN hlev
  have hζ : ∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ R p) := fun p hp => by
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun p => p ^ R p) hp
    exact ⟨_, hz.pow hN (hm.trans (mul_comm _ _))⟩
  let M₁ : PModel ℤ (fun c' : (k : Unit) → Fin n => ∏ k, (fun q : Σ _ : Unit, Fin n => x q.2) ⟨k, c' k⟩) :=
    ⟨M.X, M.ξ, M.s, M.hover, M.all,
      coordTie_reindex M.tie (fun c' => c' ()) (fun a => ⟨fun _ => a, rfl⟩) _ fun c' => by simp⟩
  obtain ⟨K₁, _, J₁, _, y₁, -, -, A, g₁, -, -, hg₁, hAf, hAR, hA, -⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l Xo c Y S R Ω Unit (fun _ => Fin n) (fun q => x q.2) M₁ f y₀ hnorm hy (hf ▸ he) hS hd hR
      (fun p hp => fullTorsion_push m.cart (Finset.dvd_prod_of_mem (fun p => p ^ R p) hp) htor) hζ
  have hg₁' : A.ξ ≫ g₁ = M.ξ := by
    rw [hg₁]
    simp [M₁]
  have hAy : A.ξ ≫ A.f = y₀ ≫ Y.j := by rw [hAf, ← Category.assoc, hg₁', hy]
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates M.ξ A.ξ₀ f A.fn := by
    have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this ⊢
    rw [← this, hAy, hy]
  have hcov : A.IsCover (letI := A.fn.toAlgebra; Module.finrank A.Ω₀ Ω) := by
    refine ⟨?_, rfl⟩
    let := A.fn.toAlgebra
    have : Module.Finite A.Ω₀ Ω := finite_of_dominates M.tie.gen f hdom
    exact Module.finrank_pos
  obtain ⟨Ω', _, _, i, K₂, _, J₂, _, y₂, B, g₂, b, Li₀, a₀, m₀, M₀, j, V₀, hg₂, hBf, hBR, hB, hb, hj, hV, hgen⟩ :=
    GlobalTheory.T.hodge_cpt_good_reduction_degree hW E H D l Xo c Y S Ω K₁ J₁ y₁ A y₀ _ hAy hd hA (by rw [hAR]; exact hζ) hcov
  have hBy : B.ξ ≫ B.f = (spMap i ≫ y₀) ≫ Y.j := by
    rw [hBf, ← Category.assoc, hg₂, Category.assoc, hAy, Category.assoc]
  obtain ⟨K₃, _, J₃, _, y₃, -, -, C, g₃, Fl, xdeg, e, -, -, hg₃, hCf, hCR, -, hC, -, -, hroot, hdR, -⟩ :=
    GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω' K₂ J₂ y₂ B (spMap i ≫ y₀) b Li₀ a₀ m₀ M₀ j V₀ _ hBy hd hB
      (fun p hp => by
        obtain ⟨ζ, hζ'⟩ := hζ p hp
        exact ⟨i ζ, by rw [hBR, hAR]; exact hζ'.map_of_injective i.injective⟩) hb hj hV hgen
  refine ⟨Ω', inferInstance, inferInstance, K₃, inferInstance, J₃, inferInstance, y₃, C, Fl, xdeg, e, ?_,
    by rw [hCR, hBR, hAR], hC, hroot, hdR⟩
  rw [hCf, Scheme.Hom.comp_apply, genPt_of_dominates hg₃, hBf, Scheme.Hom.comp_apply, genPt_of_dominates hg₂, hAf,
    Scheme.Hom.comp_apply, genPt_of_dominates hg₁]
  exact hf

end GlobalTheory.CompanionTheory.Ar.HodgeExists
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveHodgePrimeStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_curve_hodge_prime : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesWeightBoundOfFreeStatement
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_lines_weight_bound_of_free : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [Fintype (CMType H)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (p : ℕ), p ∈ S → HTFree 𝔐 p → Fl.RootLines M.xdeg e → ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → M.NefAt p mu 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt | exact GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagHeightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_flag_height : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S R.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → R.Ω), 1 ≤ D.p + D.q → Fl.RootLines R.xdeg e → Ht.FibreInput R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput | exact GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput | (intros; apply GlobalTheory.CompanionTheory.Ar.TopFibre.fibreInput <;> assumption)
end

