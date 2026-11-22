import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0057
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0055
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0056
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterOnTorsionPointsEqSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem character_on_torsion_points_eq_series : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (k : ℕ) (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Killed F.F (p ^ k) φ → Killed F.F (p ^ k) φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, ∀ φ, Killed F.F (p ^ k) φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH k κ hmul hone
  obtain ⟨inst, hsum, hzero, hkill⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  letI := inst
  obtain ⟨hfree, hfin, -⟩ := hFH k
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain (algebraMap O C)
  set J : Ideal (PS O 1 d) := Ideal.span (Set.range (mulF F.F (p ^ k))) with hJ
  let N : AddSubmonoid (PS O 1 d →ₐ[O] O) :=
    { carrier := {φ | (p ^ k) • φ = 0}
      zero_mem' := nsmul_zero _
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [nsmul_add, ha, hb, add_zero] }
  have hN : ∀ n : N, Killed F.F (p ^ k) n.1 := fun n => (hkill _ _).1 n.2
  have hNJ : ∀ n : N, ∀ u ∈ J, n.1 u = 0 := by
    intro n u hu
    have hle : J ≤ RingHom.ker n.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hN n j
    exact hle hu
  let L : N → (QF F.F (p ^ k) →ₐ[O] O) := fun n => Ideal.Quotient.liftₐ J n.1 (hNJ n)
  have hL : ∀ (n : N) (u : PS O 1 d), L n (Ideal.Quotient.mk J u) = n.1 u := fun n u => rfl
  have hLinj : Function.Injective L := by
    intro a b hab
    apply Subtype.ext
    apply AlgHom.ext
    intro u
    rw [← hL, ← hL, hab]
  haveI : Finite N := Finite.of_injective L hLinj
  let T : QF F.F (p ^ k) →ₗ[O] (N → C) :=
    LinearMap.pi fun n => (Algebra.linearMap O C).comp (L n).toLinearMap
  have hmem : ∀ f : N → C, f ∈ LinearMap.range T ↔
      ∃ u : PS O 1 d, ∀ n : N, algebraMap O C (n.1 u) = f n := by
    intro f
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨u, fun n => rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨Ideal.Quotient.mk J u, funext hu⟩
  have hfg : (LinearMap.range T).FG := Module.Finite.iff_fg.1 inferInstance
  have hspan : Submodule.span C ((LinearMap.range T : Submodule O (N → C)) : Set (N → C)) = ⊤ := by
    let e : N → (PS O 1 d →* C) := fun n =>
      ((algebraMap O C).comp (n.1 : PS O 1 d →+* O) : PS O 1 d →+* C).toMonoidHom
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      apply AlgHom.ext
      intro u
      exact hinj (DFunLike.congr_fun hab u)
    have hli : LinearIndependent C (fun n : N => (e n : PS O 1 d → C)) :=
      (linearIndependent_monoidHom (PS O 1 d) C).comp e he
    have htop := span_flip_eq_top_iff_linearIndependent.2 hli
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨u, rfl⟩
    exact (hmem _).2 ⟨u, fun n => rfl⟩
  have key := GlobalTheory.character_mem_lattice_of_comul C v O hv N (LinearMap.range T) hfg hspan ?_ ?_
    (fun n => κ n.1) (hone _ hzero)
    (fun x y => hmul _ _ _ (hN x) (hN y) ((hsum _ _ _).2 rfl))
  · obtain ⟨u, hu⟩ := (hmem _).1 key
    exact ⟨u, fun φ hφ => hu ⟨φ, (hkill _ _).2 hφ⟩⟩
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    obtain ⟨m, g, h, hgh⟩ := GlobalTheory.T.exists_sum_mul_eval_two_points_of_free_finite_quotient p C v O hv d J hfree hfin (ev (n := 2) ![F.F] u)
    refine ⟨m, fun i n => algebraMap O C (n.1 (g i)), fun i n => algebraMap O C (n.1 (h i)),
      fun i => (hmem _).2 ⟨g i, fun n => rfl⟩, fun i => (hmem _).2 ⟨h i, fun n => rfl⟩, ?_⟩
    intro x y
    obtain ⟨Φ, h0, h1, h2⟩ := (hsum x.1 y.1 (x + y).1).2 rfl
    rw [← hu, ← h2, hgh Φ x.1 y.1 h0 h1 (hNJ x) (hNJ y), map_sum]
    simp only [map_mul]
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    exact ⟨_, hu 0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CurveLogarithmsInvNatCastSmulMemStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveLogarithms_inv_natCast_smul_mem : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (N : ℕ), V.v (N : C) = 0 → ∀ a ∈ Cv X V g, (N : C)⁻¹ • a ∈ Cv X V g := by
  first | exact @GlobalTheory.RowLaw.cv_inv_natCast_smul_mem | exact GlobalTheory.RowLaw.cv_inv_natCast_smul_mem | (intros; apply GlobalTheory.RowLaw.cv_inv_natCast_smul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTransposeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspaceDim_add_split_exact_transpose : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (d r g : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O), SplitEx A B → ∀ (ρ : OE →+* Matrix (Fin d) (Fin d) O) (ρA : OE →+* Matrix (Fin r) (Fin r) O) (ρB : OE →+* Matrix (Fin g) (Fin g) O), (∀ a, B * ρ a = ρB a * B) → (∀ a, ρ a * A = A * ρA a) → ∀ τ : OE →+* C, eigDim C ρ τ = eigDim C ρA τ + eigDim C ρB τ ∧ eigDim C (fun a => (ρ a)ᵀ) τ = eigDim C ρ τ := by
  first | exact @GlobalTheory.EigAdd.eigDim_add_transpose | exact GlobalTheory.EigAdd.eigDim_add_transpose | (intros; apply GlobalTheory.EigAdd.eigDim_add_transpose <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFreeGenerators
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocalFactorFree

private theorem aux {R S M I : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite R M] [Module.Free R M]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) :
    ∃ (h : ℕ) (y : Fin h → M), LinearIndependent R (fun q : I × Fin h => (b q.1 : S) • y q.2) ∧
      ∀ m : M, m ∈ Submodule.span R (Set.range fun q : I × Fin h => (b q.1 : S) • y q.2) ↔ (1 - e) • m = 0 := by
  classical
  let f : LinearMap.range (LinearMap.mulLeft R e) →ₗ[R] (S ⧸ Ideal.span {1 - e}) :=
    (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})).toLinearMap ∘ₗ (Submodule.subtype _)
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨_, s, rfl⟩ hs
      have h1 : e * s ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.1 hs
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
      apply Subtype.ext
      change e * s = 0
      have h2 : e * (e * s) = e * s := by rw [← _root_.mul_assoc, he.eq]
      rw [← h2, ← ht]
      linear_combination t * he.mul_one_sub_self
    · intro a
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      refine ⟨⟨e * s, s, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ (e * s) = Ideal.Quotient.mk _ s
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton'.2 ⟨-s, by ring⟩
  let bA : Module.Basis I R (S ⧸ Ideal.span {1 - e}) := b.map (LinearEquiv.ofBijective f hf)
  haveI : Module.Finite R (S ⧸ Ideal.span {1 - e}) := Module.Finite.of_basis bA
  haveI : Module.Free R (S ⧸ Ideal.span {1 - e}) := Module.Free.of_basis bA
  let N : Submodule S M := Submodule.torsionBy S M (1 - e)
  haveI : Module.Finite R N := Module.Finite.of_injective (N.subtype.restrictScalars R) Subtype.val_injective
  letI : Module (S ⧸ Ideal.span {1 - e}) N := inferInstanceAs (Module (S ⧸ Submodule.span S {1 - e}) (Submodule.torsionBy S M (1 - e)))
  have hsm : ∀ (s : S) (n : N), (Ideal.Quotient.mk (Ideal.span {1 - e}) s) • n = s • n := fun _ _ => rfl
  haveI : IsScalarTower R (S ⧸ Ideal.span {1 - e}) N := ⟨fun r a n => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : r • Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) (r • s) := rfl
    rw [this, hsm, hsm, smul_assoc]⟩
  haveI : Module.Finite (S ⧸ Ideal.span {1 - e}) N := Module.Finite.of_restrictScalars_finite R _ _
  haveI : Module.IsTorsionFree (S ⧸ Ideal.span {1 - e}) N := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a n han
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : r • n = 0 := by
      rw [← algebraMap_smul (S ⧸ Ideal.span {1 - e}) r n, hc, mul_comm, mul_smul, han, smul_zero]
    have h2 : r • (n : M) = 0 := congrArg Subtype.val h1
    exact Subtype.ext ((smul_eq_zero.1 h2).resolve_left hr)
  let y := Module.finBasis (S ⧸ Ideal.span {1 - e}) N
  let B := bA.smulTower y
  have hB : (fun q : I × Fin _ => (b q.1 : S) • (y q.2 : M)) = (N.subtype.restrictScalars R) ∘ B := by
    funext q
    simp only [B, Function.comp, Module.Basis.smulTower_apply]
    rfl
  refine ⟨_, fun j => (y j : M), ?_, fun m => ?_⟩
  · rw [hB]
    exact B.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · rw [hB, Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨n, rfl⟩
      exact n.2
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩

private theorem aux2 {R S I κ : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [Fintype κ] [DecidableEq κ]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) (ρ : S →ₐ[R] Matrix κ κ R) :
    ∃ (h : ℕ) (y : Fin h → κ → R), LinearIndependent R (fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) ∧
      Submodule.span R (Set.range fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) =
        LinearMap.range (Matrix.mulVecLin (ρ e)) := by
  letI : Module S (κ → R) := Module.compHom (κ → R) (ρ : S →+* Matrix κ κ R)
  have hsm : ∀ (s : S) (v : κ → R), s • v = ρ s *ᵥ v := fun _ _ => rfl
  haveI : IsScalarTower R S (κ → R) := ⟨fun r s v => by
    rw [hsm, hsm, map_smul, Matrix.smul_mulVec]⟩
  obtain ⟨h, y, h1, h2⟩ := aux (M := κ → R) e he b
  refine ⟨h, y, h1, ?_⟩
  ext m
  refine (h2 m).trans ⟨fun hm => ⟨m, ?_⟩, ?_⟩
  · change e • m = m
    rw [sub_smul, one_smul, sub_eq_zero] at hm
    exact hm.symm
  · rintro ⟨v, rfl⟩
    change (1 - e) • e • v = 0
    rw [← mul_smul, he.one_sub_mul_self, zero_smul]

theorem exists_free_generators : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]), ∃ (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) ∧ Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) := by
  intro p _ OE _ _ _ _ _ w b κ _ _ ρ
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.padic_unit_quotient_principal_basis p OE w
  exact aux2 w.e w.idem b ρ

end GlobalTheory.LocalFactorFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupSeriesSeparatedByTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem mem_span_of_killed {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (N : ℕ)
    (h : ∀ q : QF F N, (∀ φ : QF F N →ₐ[R] R, φ q = 0) → q = 0) (f : PS R 1 d)
    (hf : ∀ φ, Killed F N φ → φ f = 0) : f ∈ Ideal.span (Set.range (mulF F N)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine h _ fun φ => ?_
  refine hf (φ.comp (Ideal.Quotient.mkₐ R _)) fun j => ?_
  have : Ideal.Quotient.mk (Ideal.span (Set.range (mulF F N))) (mulF F N j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  simp [this]

theorem mem_span_mulF_of_killed_and_eq_zero_of_tors : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → (∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) → f ∈ Ideal.span (Set.range (mulF F.F (p ^ k)))) ∧ ∀ f : PS O 1 d, (∀ φ, Tors p F.F φ → φ f = 0) → f = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hc d F hFH
  have h1 : ∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) →
      f ∈ Ideal.span (Set.range (mulF F.F (p ^ k))) :=
    fun k f hf => mem_span_of_killed F.F (p ^ k) (hFH k).2.2 f hf
  refine ⟨h1, fun f hf => ?_⟩
  have hH := ((mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2
    hc).toIsHausdorff
  refine hH.haus f fun k => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  refine (Ideal.span_le.2 ?_) (h1 k f fun φ hφ => hf φ ⟨k, hφ⟩)
  rintro _ ⟨j, rfl⟩
  exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow O d F).2.2.2 p k j

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusMemTypicalCurveSetStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_mem_typicalCurveSet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g := by
  first | exact @GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet | exact GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet | (intros; apply GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndPairPlacesStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_pair_places : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ g, HasTeich (Y.raw p) V g := by
  first | exact @GlobalTheory.TeichPair.hasTeich | exact GlobalTheory.TeichPair.hasTeich | (intros; apply GlobalTheory.TeichPair.hasTeich <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantValueCopiesEqZeroOfLowCoeff
section
set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.PowGerm

theorem nabValN_eq_zero_of_coeff_eq_zero :
    ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u f P hf
  classical
  unfold nabValN
  rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hdeg : a.degree ≤ P.totalDegree := by
    have := MvPolynomial.le_totalDegree ha
    rwa [Finsupp.degree_apply]
  rw [NabJet.constantCoeff_DmonN_congr _ cp u a _ 0 fun mo hmo => ?_,
    (NabJet.isLinearMap_DmonN (B.FK K) cp u a).map_zero, map_zero, mul_zero]
  rw [NabJet.coeff_mul_congr P.totalDegree f 0 _ (fun b hb => by rw [hf b hb, map_zero]) mo (hmo.trans hdeg), zero_mul]

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotentStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_place_basis_of_idempotent : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]) (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) → Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) → ∀ τ ∈ Emb (O := O) w.e, eigDim C (fun a : OE => (ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) ((algebraMap O C).comp τ) = h := by
  first | exact @GlobalTheory.ChF.eigDim_eq_of_basis | exact GlobalTheory.ChF.eigDim_eq_of_basis | (intros; apply GlobalTheory.ChF.eigDim_eq_of_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RangeIdempotentRankSumEigenspaceDimStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_idempotent_rank_sum_eigenspaceDim : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (g : ℕ) (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Fin g) (Fin g) O) (e : ℤ_[p] ⊗[ℤ] OE), e * e = e → ∀ (n : ℕ) (t : Fin n ≃ Emb (O := O) e), Nonempty (LinearMap.range (Matrix.mulVecLin (ρ e)) ≃ₗ[O] (Fin (∑ j, eigDim C (fun a : OE => ρ (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp ((t j : Emb (O := O) e) : OE →+* O))) → O)) := by
  first | exact @GlobalTheory.ChF.range_idempotent_equiv_sum_eigDim | exact GlobalTheory.ChF.range_idempotent_equiv_sum_eigDim | (intros; apply GlobalTheory.ChF.range_idempotent_equiv_sum_eigDim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddCurve

section Rings
variable (R : Type) [CommRing R] (l : ℕ)

abbrev Tr : Type := AdjoinRoot (Polynomial.X ^ l : Polynomial R)

abbrev Tr2 : Type := DualNumber (Tr R l)

def tt : Tr2 R l := TrivSqZeroExt.inl (AdjoinRoot.root _)

def ee : Tr2 R l := DualNumber.eps

def inc (k : Type) [CommRing k] [Algebra k R] : R →ₐ[k] Tr2 R l := IsScalarTower.toAlgHom k R (Tr2 R l)

def incD (k : Type) [CommRing k] [Algebra k R] : R →ₐ[k] DualNumber R := IsScalarTower.toAlgHom k R (DualNumber R)

variable {R l}

def cf (n : ℕ) : Tr R l →ₗ[R] R := (Polynomial.lcoeff R n).comp (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow l))

def dlog (κ : Tr2 R l) : R := cf (l - 1) (κ.snd * Ring.inverse κ.fst)

variable (R l)

end Rings

section Points
variable {k : Type} [CommRing k]

theorem algOverHom_comp {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (f : A →ₐ[k] B) (h : B →ₐ[k] C) : algOverHom h ≫ algOverHom f = algOverHom (h.comp f) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp]; rfl

theorem algOverHom_id (A : Type) [CommRing A] [Algebra k A] : algOverHom (AlgHom.id k A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

def Cv (B : Over (Sp k)) : Type 1 := ∀ (S : Type) [CommRing S] [Algebra k S], S → (algOver k S ⟶ B)

variable {B : Over (Sp k)}

def IsAdd [GrpObj B] (cu : Cv B) (l : ℕ) : Prop :=
  (∀ (S S' : Type) [CommRing S] [Algebra k S] [CommRing S'] [Algebra k S'] (ρ : S →ₐ[k] S') (s : S), s ^ l = 0 →
    algOverHom ρ ≫ cu S s = cu S' (ρ s)) ∧
  (∀ (S : Type) [CommRing S] [Algebra k S], cu S 0 = 1) ∧
  ∀ (S : Type) [CommRing S] [Algebra k S] (s s' : S), s ^ l = 0 → s' ^ l = 0 → cu S (s + s') = cu S s * cu S s'

def Along {g : ℕ} (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B) (cv : Fin g → PowerSeries k) (cu : Cv B)
    (l : ℕ) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra k S] (s : S), s ^ l = 0 → ∀ (m : ℕ) (ψ : JetR k (Fin 1 × Fin g) m →ₐ[k] S),
    (∀ j, ψ (zR m ((0 : Fin 1), j)) = Polynomial.aeval s (PowerSeries.trunc l (cv j))) → cu S s = algOverHom ψ ≫ x m

def idx {J : Type} (i j : J) : thK → J := fun I => if (2 : Fin 3) ∈ I.down then j else i

variable {R : Type} [CommRing R] [Algebra k R]

def trip (cu : Cv B) (l : ℕ) (y : algOver k R ⟶ B) : algOver k (Tr2 R l) ⟶ G3 B :=
  lift (cu _ (tt R l)) (lift (cu _ (ee R l)) (algOverHom (inc R l k) ≫ y))

def kap [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L) (cu : Cv B) (l : ℕ) (i j : L.L.ι)
    (y : algOver k R ⟶ B) : Tr2 R l :=
  valR (trip cu l y).left ((Theta B L.L).U (idx i j)) (c.t.s (idx i j)).val

def nu [GrpObj B] (cu : Cv B) (y : algOver k R ⟶ B) (U : B.left.Opens) (a : Γ(B.left, U)) : R :=
  (valR (A := DualNumber R) (cu (DualNumber R) DualNumber.eps * (algOverHom (incD R k) ≫ y)).left U a).snd *
    Ring.inverse (valR y.left U a)

end Points

end GlobalTheory.AddCurve
end
end

