import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0287
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0286
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SplitMultiplicativeHopfOrder
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceLocalizationExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0288
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeHeight
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx

theorem lie_pack (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li)
    (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li) (h₀ : M₀.IsActOf act.act ρ₀)
    (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω]
    (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap (algebraMap R Ω) ≫ x = ξ) :
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L)
      (toLi : L →ₗ[R] Li) (j : Module.Dual R L →ₗ[R] Module.Dual Ω Li),
      Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧
      (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧
      IsBaseChange Ω j ∧ (∀ u v, j u (toLi v) = algebraMap R Ω (u v)) ∧
      ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  obtain ⟨L, i1, i2, M, ρ, toLi, hf, hp, ha, hb, hpt, hρ⟩ := GlobalTheory.T.lie_model_action_subalgebra X G Ω ξ Li M₀ B act ρ₀ h₀ O R x hx
  obtain ⟨j, hj, hj'⟩ := GlobalTheory.T.dual_lattice_base_change Ω O R L Li toLi hb
  exact ⟨L, i1, i2, M, ρ, toLi, j, hf, hp, ha, hb, hpt, hj, hj', hρ⟩

theorem isIso_spMap_fracToField {Ω : Type} [Field Ω] {O : Type} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω)
    [IsFractionRing R Ω] : IsIso (spMap (fracToField R)) := by
  have hs : Function.Surjective (fracToField R) := fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    refine ⟨algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b, ?_⟩
    have h : ∀ r : R, fracToField R (algebraMap R (FractionRing R) r) = algebraMap R Ω r := fun r =>
      IsFractionRing.lift_algebraMap _ r
    rw [map_div₀, h, h]
  have : IsIso (CommRingCat.ofHom (fracToField R)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(fracToField R).injective, hs⟩
  infer_instance

theorem finite_torsT (E : Type) [Field E] [NumberField E] (N n : ℕ) (hn : n ≠ 0) : Finite (TorsT E N n) := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  exact inferInstanceAs (Finite (Fin N → (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)})))

theorem qhom_surjective (E : Type) [Field E] [NumberField E] (N n : ℕ) : Function.Surjective (qhom (E := E) N n) := fun t => by
  choose f hf using fun i => Ideal.Quotient.mk_surjective (Multiplicative.toAdd t i)
  refine ⟨Multiplicative.ofAdd f, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  exact hf i

theorem qhom_eq_one_iff (E : Type) [Field E] [NumberField E] (N n : ℕ) (y : Fin N → 𝓞 E) :
    qhom (E := E) N n (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = n • y' := by
  have h1 : qhom (E := E) N n (Multiplicative.ofAdd y) = 1 ↔ ∀ i, (n : 𝓞 E) ∣ y i := by
    constructor
    · intro h i
      have h2 := congrFun (congrArg Multiplicative.toAdd h) i
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    · intro h
      apply Multiplicative.toAdd.injective
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h i))
  rw [h1]
  constructor
  · intro h
    choose f hf using h
    exact ⟨f, by funext i; simp [hf i, nsmul_eq_mul]⟩
  · rintro ⟨y', rfl⟩ i
    exact ⟨y' i, by simp [nsmul_eq_mul]⟩

theorem chartPack_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → Nonempty (ChartPack G O c') := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hv hpq p _ hpS hHT hp2 hdisc A _ _ _ m _ hm O _ _ _ _ _ _ _ G c' hc
  obtain ⟨hΩ, hno, hic, hfr, x, hx⟩ := GlobalTheory.T.arith_variety_prime_torsion E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hv p hpS A m hm O c' hc
  haveI := hno; haveI := hic; haveI := hfr; haveI := hΩ
  haveI : CharZero (CR O y c') := ⟨fun a b h => by
    have h2 := congrArg (algebraMap (CR O y c') Ω) h
    simpa using h2⟩
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨L, i1, i2, M, ρ, toLi, j, hfin, hproj, hact, hbc, hpt, hjbc, hj, hρ⟩ :=
    lie_pack 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M (𝓞 E) 𝔐.t.act 𝔐.ρ 𝔐.act O (CR O y c') x hx
  have hR : 0 < 𝔐.R p := by have := 𝔐.R_ge p hpS; omega
  obtain ⟨Γ₁, i₁, ht₁, hp₁⟩ := GlobalTheory.T.full_torsion_injective_subalgebra 𝔐.X 𝔐.t.G 𝔐.t.semi Ω 𝔐.ξ O (CR O y c') x hx _ G.t₁.pt p (p ^ 𝔐.R p)
    (Fact.out : p.Prime).one_lt.le (dvd_pow_self p hR.ne') (𝔐.tors p hpS) G.t₁.inj G.t₁.onto
  obtain ⟨Γ₂, i₂', ht₂, hp₂⟩ := GlobalTheory.T.full_torsion_injective_subalgebra 𝔐.X 𝔐.t.G 𝔐.t.semi Ω 𝔐.ξ O (CR O y c') x hx _ G.t₂.pt (p ^ 𝔐.R p) (p ^ 𝔐.R p)
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos) dvd_rfl (𝔐.tors p hpS) G.t₂.inj G.t₂.onto
  have hn0 : p ^ 𝔐.R p ≠ 0 := (pow_pos (Fact.out : p.Prime).pos _).ne'
  have hmem : ∀ z : Ω, z ^ (p ^ 𝔐.R p) = 1 → z ∈ CR O y c' := fun z hz => by
    have hi : IsIntegral ℤ z := IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) (hz ▸ isIntegral_one)
    have h := IsIntegralClosure.algebraMap_mk' A z hi
    rw [← h, IsScalarTower.algebraMap_apply A O Ω]
    exact (CR O y c').algebraMap_mem _
  have hz1 : G.ζ ^ (p ^ 𝔐.R p) = 1 := G.ζ_prim.pow_eq_one
  have hz2 : (G.ζ⁻¹) ^ (p ^ 𝔐.R p) = 1 := by rw [inv_pow, hz1, inv_one]
  have hne : G.ζ ≠ 0 := G.ζ_prim.ne_zero hn0
  obtain ⟨ζ, hζ⟩ : ∃ u : (CR O y c')ˣ, ((u : CR O y c') : Ω) = G.ζ :=
    ⟨⟨⟨G.ζ, hmem _ hz1⟩, ⟨G.ζ⁻¹, hmem _ hz2⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩
  haveI hfinT : Finite (TorsT E (D.p + D.q) (p ^ 𝔐.R p)) := finite_torsT E _ _ hn0
  have hsurj : Function.Surjective (qhom (E := E) (D.p + D.q) (p ^ 𝔐.R p)) := qhom_surjective E _ _
  have hker : ∀ y₁, qhom (E := E) (D.p + D.q) (p ^ 𝔐.R p) (Multiplicative.ofAdd y₁) = 1 ↔ ∃ y', y₁ = (p ^ 𝔐.R p) • y' :=
    qhom_eq_one_iff E _ _
  haveI hiso := isIso_spMap_fracToField (CR O y c')
  have hlin : ∀ (a : 𝓞 E) y₁, (Γ₂.pt (qhom _ _ (Multiplicative.ofAdd (a • y₁)))).left ≫ i₂' =
        (Γ₂.pt (qhom _ _ (Multiplicative.ofAdd y₁))).left ≫ i₂' ≫ (𝔐.t.act.act a).left := by
    intro a y₁
    rw [← cancel_epi (spMap (fracToField (CR O y c')))]
    have h1 := hp₂ (qhom _ _ (Multiplicative.ofAdd (a • y₁)))
    have h2 := hp₂ (qhom _ _ (Multiplicative.ofAdd y₁))
    have h3 : (G.t₂.pt (qhom _ _ (Multiplicative.ofAdd (a • y₁)))).left =
        (G.t₂.pt (qhom _ _ (Multiplicative.ofAdd y₁))).left ≫ (𝔐.t.act.act a).left :=
      congrArg (fun f => f.left) (G.t₂.lin a y₁)
    rw [← h1, h3, h2]
    simp only [Category.assoc]
  have hzpow : ζ ^ (p ^ 𝔐.R p) = 1 := by
    apply Units.ext
    apply Subtype.ext
    show (((ζ : CR O y c') ^ (p ^ 𝔐.R p) : CR O y c') : Ω) = 1
    rw [SubmonoidClass.coe_pow, hζ, hz1]
  have hbar : ∀ a : 𝓞 E, RingOfIntegers.mapRingEquiv (HT.cmConj E) a = H.bar a := fun a => by
    ext
    rw [H.bar_eq]
    rfl
  obtain ⟨Dh, hDe, hHT⟩ := GlobalTheory.T.HTChartExists_holds (CR O y c') Ω E (HT.cmConj E) p (𝔐.R p) (D.p + D.q) _ Γ₂ 𝔐.X 𝔐.t.G x i₂' ht₂ hsm
    𝔐.t.act.act 𝔐.t.act.hom L M ρ hact (Module.Dual Ω 𝔐.Li) j hjbc (qhom _ _) hsurj hker hlin ζ hzpow G.e G.alt
    (fun a y₁ z => by rw [hbar]; exact G.adj a y₁ z) G.e_surj G.e_inj
  have hform : ∀ (b : 𝓞 E) (w : Module.Dual (CR O y c') L), j (w ∘ₗ ρ b) = j w ∘ₗ 𝔐.ρ b := by
    intro b w
    ext e
    refine hbc.inductionOn e (fun e => j (w ∘ₗ ρ b) e = (j w ∘ₗ 𝔐.ρ b) e) (by simp) ?_ ?_ ?_
    · intro v
      simp only [LinearMap.comp_apply]
      rw [hj, ← hρ, hj]
      rfl
    · intro s n hn
      simp only [map_smul, hn]
    · intro n₁ n₂ h₁ h₂
      simp only [map_add, h₁, h₂]
  have hact' : ∀ (a : 𝓞 E) (u : Module.Dual Ω 𝔐.Li), Dh.ρΩ a u = u ∘ₗ 𝔐.ρ (H.bar a) := by
    intro a u
    refine hjbc.inductionOn u (fun u => Dh.ρΩ a u = u ∘ₗ 𝔐.ρ (H.bar a)) (by simp) ?_ ?_ ?_
    · intro w
      rw [hHT.2.1, hbar, hform]
    · intro s n hn
      rw [map_smul, hn]
      rfl
    · intro n₁ n₂ h₁ h₂
      rw [map_add, h₁, h₂]
      rfl
  exact ⟨{ x := x, x_gen := hx, L := L, fin := hfin, proj := hproj, M := M, ρ := ρ, act := hact, toLi := toLi, toLi_bc := hbc,
           toLi_pt := hpt, j := j, j_bc := hjbc, j_apply := hj, Γ₁ := Γ₁, i₁ := i₁, tors₁ := ht₁, pts₁ := hp₁,
           Γ₂ := Γ₂, i₂ := i₂', tors₂ := ht₂, pts₂ := hp₂, ζ := ζ, ζ_eq := hζ, Dh := Dh, Dh_e := hDe, Dh_act := hact', isHT := hHT }⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelHodgeRelay
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_model_hodge_relay : GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ GlobalTheory.CompanionTheory.Ar.GR.IsTight v p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) := by
  first | exact @PositivityTheory.Xgn.tight_hopf_order_test | exact PositivityTheory.Xgn.tight_hopf_order_test
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeHeight
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li)) := by
  first | exact @PositivityTheory.Xgn.sequence_localization_exists | exact PositivityTheory.Xgn.sequence_localization_exists
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeRelayStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_relay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_log_period_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ z ∈ Flat.punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem | exact GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Geo.SncCoordsSide

theorem coordsStatement_side : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement :=
  GlobalTheory.CompanionTheory.Geo.SncCoords.coordsStatement

end GlobalTheory.CompanionTheory.Geo.SncCoordsSide
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_torsion_integrally_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (s : Sp Ω ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (_ : SABMap o.t t ξ) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n → IsIntegrallyClosed (X.presheaf.stalk q.1) → IsNoetherianRing (X.presheaf.stalk q.1) → M.IsHTFormAt n q 0 ∧ (0 < D.p + D.q → ∃ ζ : Ω, IsPrimitiveRoot ζ n) ∧ M.htOm t.PP.L n q = M.htLat n q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OmLink.htOm_eq_htLat | exact GlobalTheory.CompanionTheory.Ar.OmLink.htOm_eq_htLat | (intros; apply GlobalTheory.CompanionTheory.Ar.OmLink.htOm_eq_htLat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularRelayStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_triangular_relay : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (E₀ F : Type) [AddCommGroup E₀] [Module K E₀] [AddCommGroup F] [Module L F] (j : E₀ →+ F) (S : Type) [Finite S] (r : S → ℕ) (V : S → Submodule K E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ), GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω := K) (Ω' := L) j V b d → ∀ (e : ∀ s, Fin (r s) → E₀), (∀ s l, e s l ∈ V s) → (∀ s, LinearIndependent L fun l => j (e s l)) → ∃ v Tm : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L, (∀ s k, v s k k = 1) ∧ (∀ s l k, l < k → v s l k = 0) ∧ AlgebraicIndependent K (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin K (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) L = d ∧ (∀ s i, b s i = ∑ m, Tm s i m • ∑ l, v s l m • j (e s l)) ∧ (∀ s i m, i < m → Tm s i m = 0) ∧ ∀ s i, Tm s i i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay | exact GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

open GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section Noeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {κ : Type} [Finite κ]

theorem isNoetherianRing_chart (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x) (c : κ)
    (hc : x c ≠ 0) (U : X.Opens) (hU : IsAffineOpen U)
    (hUm : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (hη : genPt ξ ∈ U) :
    IsNoetherianRing Γ(X, U) := by
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  let A : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  have hreg : ∀ a : Ω, a ∈ A ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* A := (ev ξ U hη).codRestrict A
    fun s => (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    have h0 : ev ξ U hη s = 0 := congrArg Subtype.val hs
    refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun q hq => ?_
    apply hT.gen.inj ⟨q, sp q hq⟩
    have h1 := genMap_germ hη ⟨q, sp q hq⟩ hq s
    rw [h0] at h1
    refine h1.trans ?_
    simp only [map_zero]
    exact (map_zero (genMap ξ ⟨q, sp q hq⟩)).symm
  have hsurj : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp a ((hreg a).1 ha)
    exact ⟨s, Subtype.ext hs⟩
  haveI : Algebra.FiniteType ℤ A :=
    (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  exact isNoetherianRing_of_ringEquiv A (RingEquiv.ofBijective ρ ⟨hinj, hsurj⟩).symm

theorem isLocallyNoetherian_of_coordTie (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) : IsLocallyNoetherian X := by
  have key : ∀ p : X, ∃ U : X.affineOpens, p ∈ U.1 ∧ IsNoetherianRing Γ(X, U.1) := by
    intro p
    obtain ⟨c, hch⟩ := hT.cover ⟨p, hall p⟩
    obtain ⟨U, hU, hUm⟩ := hT.affine c hch.1
    have hp : p ∈ U := (hUm p).2 ⟨hall p, hch⟩
    exact ⟨⟨U, hU⟩, hp, isNoetherianRing_chart ξ x hT c hch.1 U hU hUm ((hall p).mem_open U.isOpen hp)⟩
  choose S hS hN using key
  exact isLocallyNoetherian_of_affine_cover (S := S)
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hS p⟩) hN

end Noeth

section Form

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_homog_form_point (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω)
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (V : X.Opens) (hV : genPt ξ ∈ V) :
    ∃ (f : MRing J) (d : K → ℕ), IsMultiHomog f d ∧ f ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w f ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, CoordsAt ξ y z w ∧ centre z ∈ V := by
  classical
  obtain ⟨c, hch⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  have hcx := hch.1
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcx k (Finset.mem_univ k)
  obtain ⟨U, hU, hUm⟩ := hT.affine c hcx
  have hη : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hch⟩
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  have hreg : ∀ a : Ω, a ∈ chartRingZ y c ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    have h := hT.ring c hcx a
    rw [show (Algebra.adjoin ℤ (Set.range fun j : (∀ k, J k) => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) =
      chartRingZ y c from segre_chart y c hc] at h
    refine h.trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* chartRingZ y c := (ev ξ U hη).codRestrict (chartRingZ y c)
    fun s => (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩
  obtain ⟨s, hsV, hsη⟩ := hU.exists_basicOpen_le (V := V) ⟨genPt ξ, hV⟩ hη
  have ha0 : ev ξ U hη s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hη).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨g₀, hg₀⟩ := ratMap_surjective y c (ρ s)
  obtain ⟨m, G₀, hG₀, eG⟩ := exists_form c g₀
  have hy₀ : aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g₀ = ev ξ U hη s := by
    rw [← ratMap_coe, hg₀]
    rfl
  have hf0 : aeval y (G₀ * cMon c 1) ≠ 0 := by
    rw [map_mul, aeval_cMon, ← eG Ω y hc, hy₀]
    exact mul_ne_zero (mul_ne_zero ha0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  refine ⟨G₀ * cMon c 1, m + 1, homog_mul hG₀ (homog_cMon c 1), fun hmem => hf0 ?_, fun w hw hne => ?_⟩
  · have h := aeval_scaled y (fun _ => 1) (G₀ * cMon c 1)
    have h0 : mConeMap y (G₀ * cMon c 1) = 0 := hmem
    rw [h0, map_zero] at h
    simpa only [mul_one] using h
  have hne' : aeval w (G₀ * cMon c 1) ≠ 0 := by
    rw [← evC_eq_aeval]
    exact hne
  rw [map_mul, aeval_cMon] at hne'
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne') k (Finset.mem_univ k)
    simpa using this
  obtain ⟨e, he⟩ := exists_chartEval y c hc w hw hwc
  obtain ⟨z, hz, hval⟩ := exists_pt hU (e.comp ρ)
  have hval' : ∀ k i, ∃ s : Γ(X, U), ev ξ U hη s = y ⟨k, i⟩ / y ⟨k, c k⟩ ∧
      (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) = w ⟨k, i⟩ / w ⟨k, c k⟩ := by
    intro k i
    have hm : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c := Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp _ ((hreg _).1 hm)
    refine ⟨s, hs, ?_⟩
    have e1 : ρ s = ratMap y c (MvPolynomial.X ⟨k, i⟩) := Subtype.ext (by rw [ratMap_coe, aeval_X]; exact hs)
    rw [hval]
    change e (ρ s) = _
    rw [e1, he, aeval_X]
  have hs0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) ≠ 0 := by
    rw [hval]
    change e (ρ s) ≠ 0
    rw [← hg₀, he]
    intro h0
    apply left_ne_zero_of_mul hne'
    rw [← eG ℂ w hwc, h0, zero_mul]
  refine ⟨z, ⟨fun k => ⟨c k, (IsUnit.mk0 _ (hwc k))⟩, fun k c₀ hu => ?_⟩, hsV ?_⟩
  · have hw0 : w ⟨k, c₀⟩ ≠ 0 := hu.ne_zero
    obtain ⟨sv, hsv, hev⟩ := hval' k c₀
    have hev0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz sv) ≠ 0 := by
      rw [hev]
      exact div_ne_zero hw0 (hwc k)
    have hy0 : y ⟨k, c₀⟩ ≠ 0 := by
      intro h0
      apply hev0
      have h1 : ρ sv = 0 := Subtype.ext (by
        change ev ξ U hη sv = 0
        rw [hsv, h0, zero_div])
      rw [hval]
      change e (ρ sv) = 0
      rw [h1, map_zero]
    refine ⟨hy0, fun i => ?_⟩
    obtain ⟨su, hsu, heu⟩ := hval' k i
    refine ⟨w ⟨k, i⟩ / w ⟨k, c₀⟩, ?_, by field_simp⟩
    have h := valAt_quot hη sp z hz su sv hev0
    rw [hsu, hsv, heu, hev, div_div_div_cancel_right₀ (hc k), div_div_div_cancel_right₀ (hwc k)] at h
    exact h
  · exact (Scheme.mem_basicOpen X s _ hz).2
      (isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (IsUnit.mk0 _ hs0))

end Form

end GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

theorem GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c), A.ξ ≫ A.f = x ≫ Y.j → Mono (spMap β) → ∃ (b : MRing ι) (d : K → ℕ), IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w b ≠ 0 → ∃ z : Spec (CommRingCat.of ℂ) ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ ι _ y A x hx _
  haveI : IsLocallyNoetherian A.X := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.isLocallyNoetherian_of_coordTie A.ξ _ A.tie A.all
  let V : A.X.Opens := ⟨abLocus A.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian A.t.G A.t.semi⟩
  have hV : genPt A.ξ ∈ V := by
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 (genPt A.ξ)).1 ?_
    have h1 : A.f (genPt A.ξ) = Y.j (x (IsLocalRing.closedPoint Ω)) := by
      have := congrArg (fun g : Sp Ω ⟶ Y.X => g (IsLocalRing.closedPoint Ω)) hx
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (this.trans (Scheme.Hom.comp_apply _ _ _))
    rw [h1]
    exact GlobalTheory.ModelScope.range_j_subset_abLocus Y ⟨_, rfl⟩
  obtain ⟨b, d, hb, hbI, hw⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_homog_form_point A.ξ y A.tie V hV
  refine ⟨b, d, hb, hbI, fun w hwm hne => ?_⟩
  obtain ⟨z, hz, hzV⟩ := hw w hwm hne
  exact ⟨z, hz, hzV⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartIntegralStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_integral : PointHT → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left) (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R), IsHTChartOf Dc Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → 2 * Module.finrank R L = Module.finrank ℤ D.La → IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing R →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt R).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ (p ^ n) : k) = f (algebraMap R _ (ζ₀ : R)) ∧ ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) → (if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → Dc.HasTestPoints κ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.hasTestPoints_of_tate | exact GlobalTheory.CompanionTheory.Ar.HT.hasTestPoints_of_tate | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.hasTestPoints_of_tate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_weil_local : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (q : Cpt ξ), (∃ U : X.Opens, q.1 ∈ U ∧ ∃ w : (Over.mk ξ ⟶ G) → Module.Dual Ω E, ∀ y, y ^ n = 1 → ∀ q' : Cpt ξ, q'.1 ∈ U → M.IsHTAt L n y q' (w y)) ∧ ∀ (y : Over.mk ξ ⟶ G) (w w' : Module.Dual Ω E), y ^ n = 1 → M.IsHTAt L n y q w → (M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts | exact GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts | (intros; apply GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LemmaBTHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LemmaBT_holds : GlobalTheory.CompanionTheory.Ar.BT.LemmaBT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | exact GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.lemmaBT_holds <;> assumption)
end

