import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0071
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0074
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNotMemForallMem

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartProjectionRespectsOrthogonalityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_projection_respects_orthogonality : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegData W I) (Av : Out.PolAV (Spec (CommRingCat.of (FractionRing W)))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D Av G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∀ τ : PtHom (spMap β) (spMap β) G D.toPre.P.A, (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ (U.gt 0).pG.left) → ∀ n : ℕ, Transfer n U.cubG D.toPre.cub τ := by
  first | exact @GlobalTheory.AlphaPair.transfer_of_unif | exact GlobalTheory.AlphaPair.transfer_of_unif | (intros; apply GlobalTheory.AlphaPair.transfer_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPMultiplicativeCharacterEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alphaP_multiplicativeCharacter_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (u : ∀ (A : Type) [CommRing A] [Algebra Ω A], A → Aˣ), (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 → u B (f a) = Units.map (f : A →* B) (u A a)) → (∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → u A (a + a') = u A a * u A a') → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → u A a = 1 := by
  first | exact @GlobalTheory.AlphaChar.char_eq_one | exact GlobalTheory.AlphaChar.char_eq_one | (intros; apply GlobalTheory.AlphaChar.char_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubicalWeilTrivialOfLocalArtinianPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalWeil_trivial_of_localArtinian_points : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (n : ℕ), IsFinite ((𝟙 G) ^ n : G ⟶ G).left → ∀ (D : Type) [CommRing D] [Algebra Ω D] [Module.Finite Ω D] (x : overAt s D ⟶ G), x ^ n = 1 → (∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ (f : D →ₐ[Ω] A) (y : overAt s A ⟶ G), y ^ n = 1 → CubWeil c n (homAt s f ≫ x) y 1) → ∀ (T' : Over S) (ρ : T' ⟶ overAt s D) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1 := by
  first | exact @GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian | exact GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian | (intros; apply GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DegenerateDirectionOfNotNondegenerateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerate_direction_of_not_nondegenerate : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (d : ℕ) (Y : FBChart C V O d) (R₀ : Type) [CommRing R₀] (j : R₀ →+* V.RR) (F : Fin d → PS R₀ 2 d) (ph2 : PS R₀ 3 d), (∀ i, MvPowerSeries.constantCoeff (F i) = 0) → (∀ i, Y.B.G.F i = MvPowerSeries.map (V.RR.subtype.comp j) (F i)) → Y.B.ph2 = MvPowerSeries.map (V.RR.subtype.comp j) ph2 → ∀ (Ω : Type) [Field Ω] (ρ : V.RR →+* Ω), (∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C)) → ¬ NDG Y → Degenerate V.l (fun i => MvPowerSeries.map (ρ.comp j) (F i)) (MvPowerSeries.map (ρ.comp j) ph2) := by
  first | exact @GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg | exact GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg | (intros; apply GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOneOfTangentVectorEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_tangent_vector_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G), IsAlpha p s G g → g (DualNumber Ω) DualNumber.eps = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → g A a = 1 := by
  first | exact @GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent | exact GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent | (intros; apply GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvalPowerSeriesEqOneOfTwoAxesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalPowerSeries_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  first | exact @GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | exact GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | (intros; apply GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAlgClosedResidueFieldValuedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosed_residueField_valuedField : ∀ (C : Type) [Field C] (V : VF C), IsAlgClosed C → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω V.l) (ρ : V.RR →+* Ω), ∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C) := by
  first | exact @GlobalTheory.AlphaPair.ResField.exists_residueField | exact GlobalTheory.AlphaPair.ResField.exists_residueField | (intros; apply GlobalTheory.AlphaPair.ResField.exists_residueField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChartPointNilpotentCoordinates
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetPt

section Rho

variable {V Ω : Type} [CommRing V] [CommRing Ω] (β : V →+* Ω)

def Compat {B A : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] (ψ : B →+* A) : Prop :=
  ∀ v : V, ψ (algebraMap V B v) = algebraMap Ω A (β v)

variable {β}

theorem Compat.left {B B' A : Type} [CommRing B] [Algebra V B] [CommRing B'] [Algebra V B'] [CommRing A] [Algebra Ω A]
    {ψ : B →+* A} (h : Compat β ψ) (f : B' →ₐ[V] B) : Compat β (ψ.comp (f : B' →+* B)) := fun v => by
  rw [RingHom.comp_apply, RingHom.coe_coe, f.commutes, h v]

theorem Compat.right {B A A' : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A']
    {ψ : B →+* A} (h : Compat β ψ) (g : A →ₐ[Ω] A') : Compat β ((g : A →+* A').comp ψ) := fun v => by
  rw [RingHom.comp_apply, h v, RingHom.coe_coe, g.commutes]

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

def rho {B A : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] (ψ : B →+* A) (h : Compat β ψ) :
    overAt (spMap β) A ⟶ overAt (𝟙 (Sp V)) B :=
  Over.homMk (spMap ψ) (by
    change spMap ψ ≫ spMap (algebraMap V B) ≫ 𝟙 _ = spMap (algebraMap Ω A) ≫ spMap β
    rw [Category.comp_id, sp_comp, sp_comp]
    congr 1
    exact RingHom.ext h)

theorem rho_homAt {B B' A : Type} [CommRing B] [Algebra V B] [CommRing B'] [Algebra V B'] [CommRing A] [Algebra Ω A]
    {ψ : B →+* A} (h : Compat β ψ) (f : B' →ₐ[V] B) :
    rho ψ h ≫ homAt (𝟙 (Sp V)) f = rho (ψ.comp (f : B' →+* B)) (h.left f) :=
  Over.OverMorphism.ext (sp_comp _ _)

theorem homAt_rho {B A A' : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A']
    {ψ : B →+* A} (h : Compat β ψ) (g : A →ₐ[Ω] A') :
    homAt (spMap β) g ≫ rho ψ h = rho ((g : A →+* A').comp ψ) (h.right g) :=
  Over.OverMorphism.ext (sp_comp _ _)

def co {d m : ℕ} {A : Type} [CommRing A] (ψ : Jet V (Fin 1 × Fin d) m →+* A) : Fin d → A :=
  fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))

theorem eq_of_co {d m : ℕ} {A : Type} [CommRing A] [Algebra Ω A] {ψ ψ' : Jet V (Fin 1 × Fin d) m →+* A}
    (h : Compat β ψ) (h' : Compat β ψ') (e : co ψ = co ψ') : ψ = ψ' := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun v => (h v).trans (h' v).symm) ?_)
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact congrFun e j

theorem jetMap_X {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ') (i : κ) :
    (jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i) := by
  change Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  change MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X]

theorem exists_jet {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [CommRing A] [Algebra Ω A] (a : κ → A)
    (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (m : ℕ) (ψ : Jet V κ m →+* A), Compat β ψ ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i := by
  have hn : IsNilpotent (Ideal.span (Set.range a)) := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact ha i
  obtain ⟨m, hm⟩ := hn
  obtain ⟨ψ, hψ, -⟩ := (GlobalTheory.AlphaPair.JetEv.jet_hom_spec V Ω A β κ m).1 a (by rw [pow_succ, hm, zero_mul]; rfl)
  exact ⟨m, ψ, hψ⟩

theorem exists_jet_one {d : ℕ} {A : Type} [CommRing A] [Algebra Ω A] (a : Fin d → A)
    (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (m : ℕ) (ψ : Jet V (Fin 1 × Fin d) m →+* A), Compat β ψ ∧ co ψ = a := by
  obtain ⟨m, ψ, h, e⟩ := exists_jet (β := β) (fun q : Fin 1 × Fin d => a q.2) fun q => ha q.2
  exact ⟨m, ψ, h, funext fun j => e (0, j)⟩

variable {G : Over (Sp V)} {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}

theorem lift_add (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ} (ψ : Jet V (Fin 1 × Fin d) m →+* A) (h : Compat β ψ)
    {n : ℕ} (hn : m ≤ n) :
    ∃ (χ : Jet V (Fin 1 × Fin d) n →+* A) (hχ : Compat β χ), co χ = co ψ ∧ rho χ hχ ≫ x n = rho ψ h ≫ x m := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨ψ, h, rfl, rfl⟩
  | succ n _ ih =>
    obtain ⟨χ, hχ, e, e'⟩ := ih
    refine ⟨_, hχ.left jetTrunc, e, ?_⟩
    rw [← rho_homAt hχ, Category.assoc, hx, e']

theorem indep (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m n : ℕ} {ψ : Jet V (Fin 1 × Fin d) m →+* A} (h : Compat β ψ)
    {ψ' : Jet V (Fin 1 × Fin d) n →+* A} (h' : Compat β ψ') (e : co ψ = co ψ') :
    rho ψ h ≫ x m = rho ψ' h' ≫ x n := by
  obtain ⟨χ, hχ, e₁, e₂⟩ := lift_add hx ψ h (le_max_left m n)
  obtain ⟨χ', hχ', e₁', e₂'⟩ := lift_add hx ψ' h' (le_max_right m n)
  obtain rfl : χ = χ' := eq_of_co hχ hχ' (by rw [e₁, e₁', e])
  rw [← e₂, ← e₂']

end Rho

section Main

variable {V Ω : Type} [CommRing V] [Field Ω] (β : V →+* Ω) {G : Over (Sp V)} [GrpObj G] {d : ℕ}
  (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G)

open Classical in

def ptOf : PtFam (spMap β) G d := fun A _ _ a =>
  if h : ∃ p : (m : ℕ) × (Jet V (Fin 1 × Fin d) m →+* A), Compat β p.2 ∧ co p.2 = a then
    rho h.choose.2 h.choose_spec.1 ≫ x h.choose.1
  else 1

variable {β x}

theorem ptOf_co (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ} {ψ : Jet V (Fin 1 × Fin d) m →+* A} (h : Compat β ψ)
    {a : Fin d → A} (e : co ψ = a) : ptOf β x A a = rho ψ h ≫ x m := by
  have hh : ∃ p : (m : ℕ) × (Jet V (Fin 1 × Fin d) m →+* A), Compat β p.2 ∧ co p.2 = a := ⟨⟨m, ψ⟩, h, e⟩
  rw [ptOf, dif_pos hh]
  exact indep hx _ h (hh.choose_spec.2.trans e.symm)

end Main

end GlobalTheory.AlphaPair.JetPt

open GlobalTheory.AlphaPair.JetPt in

theorem GlobalTheory.AlphaPair.exists_jetPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), IsChartG t (𝟙 (Sp V)) d F act tg uv x → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω), ∃ P : PtFam (spMap β) t.G d, IsJetPt β x P ∧ IsPtLaw (spMap β) t.G (fun j => MvPowerSeries.map β (F j)) P := by
  intro E _ _ _ H V _ t d F act tg uv x hc hF Ω _ β
  refine ⟨ptOf β x, fun A _ _ m ψ h => ?_, fun A B _ _ _ _ f a ha => ?_, fun A _ _ => ?_, fun A _ _ a b ha hb => ?_⟩
  · exact congrArg CommaMorphism.left (ptOf_co hc.trunc (ψ := ψ) h rfl)
  · obtain ⟨m, ψ, h, rfl⟩ := exists_jet_one (β := β) a ha
    rw [ptOf_co hc.trunc h rfl, ptOf_co hc.trunc (h.right f) (a := fun j => f (co ψ j)) rfl, ← Category.assoc, homAt_rho]
  · have h : Compat β ((algebraMap Ω A).comp β) := fun v => rfl
    rw [ptOf_co hc.trunc (h.left (jetAug : Jet V (Fin 1 × Fin d) 0 →ₐ[V] V))
      (funext fun j => by simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetAug_X, map_zero, Pi.zero_apply]),
      ← rho_homAt h, Category.assoc, hc.zero, MonObj.comp_one]
  · obtain ⟨m, ψ, h, e⟩ := exists_jet (β := β) (fun q : Fin 2 × Fin d => ![a, b] q.1 q.2) (by
      rintro ⟨i, j⟩
      fin_cases i
      exacts [ha j, hb j])
    have hi : ∀ i : Fin 2, ptOf β x A (![a, b] i) = rho ψ h ≫ jptG t (𝟙 (Sp V)) d x m i := fun i => by
      rw [jptG, ← Category.assoc, rho_homAt]
      refine ptOf_co hc.trunc _ (funext fun j => ?_)
      simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetCopy, jetMap_X, e]
    have h0 : ptOf β x A a = _ := hi 0
    have h1 : ptOf β x A b = _ := hi 1
    rw [h0, h1, ← MonObj.comp_mul, ← hc.law m, ← Category.assoc, rho_homAt]
    refine ptOf_co hc.trunc _ (funext fun j => ?_)
    have h3 := ((GlobalTheory.AlphaPair.JetEv.jet_hom_spec V Ω A β (Fin 2 × Fin d) m).2 ψ h).2.2 (F j)
    simp only [e] at h3
    simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetSubstP, jetMap_X]
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.cc_psTrunc, hF, map_zero, sub_zero]
    exact h3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGeneratorOfRosatiAdjointLambdaBundle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosGen

private theorem lbIso_of_local {O : Type} [CommRing O] [IsLocalRing O] {A : Over (Geo.Tor.Sp O)} [GrpObj A]
    [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (f g : A ⟶ A) (h : Out.RosatiAdj A L f g) :
    Geo.Tor.LBIso (cubeLB A ![fst A A ≫ f, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ g] L) := by
  obtain ⟨U, hs, t, ht⟩ := h (IsLocalRing.closedPoint O)
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hs
  obtain ⟨n, hn⟩ : ∃ n : (A ⊗ A).left ⟶ ((A ⊗ A).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift ((A ⊗ A).hom ⁻¹ᵁ U).ι (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι, hU]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_gen hL (φ' := Out.rosatiφ A f g) (ε' := Out.rosatiε)
    (fun V _ k => Finset.prod_congr rfl fun i _ => by
      show k (n ≫ _ ≫ _) ^ _ = k _ ^ _
      rw [← Category.assoc, hn, Category.id_comp])
    (LB.pullGen L _ _ t n) (DVR.pullGen_isGen _ _ _ _ ht n)
  exact GlobalTheory.RosLam.lbIso_of_gen hL f g u hu

private theorem prod_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (x y : T ⟶ G)
    {U : Type 1} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have key := GlobalTheory.NormRos.prod_square x y (U := Multiplicative (FreeAbelianGroup (T.left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift fun ψ : T.left ⟶ G.left => Additive.ofMul (h ψ))) key
  simpa only [map_mul, map_inv, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply,
    toAdd_ofAdd, FreeAbelianGroup.lift_apply_of, toMul_ofMul] using k

theorem exists_gen_of_rosatiAdj : ∀ (O : Type) [CommRing O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)) (Z : Scheme.{0}) (Q : LB Z) (ψ₂ : (P.A ⊗ P.A).left ⟶ Z), Q.IsLB → Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) → ∀ f f' : P.A ⟶ P.A, IsMonHom f → IsMonHom f' → Out.RosatiAdj P.A P.L f f' → ∃ t : LB.Gen (LB.LinComb Q (K := Fin 2) ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]), t.IsGen := by
  intro O _ _ P Z Q ψ₂ hQ hI f f' _ _ h
  have := P.isAb.comm
  have H := lbIso_of_local P.isLB f f' h
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, h₄, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ : (abelian₂ P.A P.L).IsLB ∧ cl (abelian₂ P.A P.L) = _ := h₅ _ _ P.L P.isLB _ _ _
  obtain ⟨q, q'⟩ : (Q.pull ψ₂).IsLB ∧ cl (Q.pull ψ₂) = _ := h₅ _ _ Q hQ _ _ _
  have e₀ : pl ψ₂ (cl Q) = cl (abelian₂ P.A P.L) := by
    rw [(h₁ _ _ _ a q).2 hI, q']; simp
  have key : ∀ x y : P.A ⊗ P.A ⟶ P.A, (cubeLB P.A ![x, y] P.L).IsLB ∧
      pl ((lift x y).left ≫ ψ₂) (cl Q) = cl (cubeLB P.A ![x, y] P.L) := fun x y => by
    obtain ⟨b, b'⟩ : (cubeLB P.A ![x, y] P.L).IsLB ∧ cl (cubeLB P.A ![x, y] P.L) = _ := h₅ _ _ P.L P.isLB _ _ _
    refine ⟨b, ?_⟩
    rw [h₄, e₀, a', b']
    have p₁ := prod_two x y (fun φ => pl φ (cl P.L))
    have p₂ := prod_two (fst P.A P.A) (snd P.A P.A) (fun φ => pl φ (cl P.L))
    refine Eq.trans (congrArg (pl (lift x y).left) p₂) (Eq.trans ?_ p₁.symm)
    simp only [map_mul, map_inv, ← h₄, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd]
  obtain ⟨c, c'⟩ := h₅ _ _ Q hQ (Fin 2)
    ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]
  refine (h₂ _ _ c).1 ?_
  rw [c', Fin.prod_univ_two]
  show pl ((lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂) (cl Q) ^ (1 : ℤ) *
    pl ((lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂) (cl Q) ^ (-1 : ℤ) = 1
  rw [(key _ _).2, (key _ _).2, (h₁ _ _ _ (key _ _).1 (key _ _).1).2 H]
  simp

end GlobalTheory.RosGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsTorusExtensionOnPointsModIdealStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTorusExtensionOnPoints_mod_ideal : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  first | exact @GlobalTheory.TorExtPoints.exists_isTorExt | exact GlobalTheory.TorExtPoints.exists_isTorExt | (intros; apply GlobalTheory.TorExtPoints.exists_isTorExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairs
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PlaceProj

theorem exists_lim_pair {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
    (ρ : O →+* Matrix (Fin dd) (Fin dd) C) (hρ : ∀ a v, linAct (Y.B.A.act a) v = (ρ a).mulVec v) :
    ∃ M : Fin 2 → Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V (M 0) (M 1) ∧ IsEnd (Y.raw p) V (M 1) (M 0) ∧
      ∀ g, ∃ (ε : O) (a : ℕ → O), IsLim V ρ a (M g) ∧ (∃ y, ε * ε - ε = (V.l : O) * y) ∧
        (∀ t, V.MM (p.em g t ε - 1)) ∧ (∀ x : O, (∀ t, V.MM (p.em g t x)) → ∃ y, ε * x = (V.l : O) * y) ∧
        (∀ m, ∃ y, a m * a m - a m = (V.l : O) ^ m * y) ∧ ∀ m, ∃ y, a m - ε = (V.l : O) * y := by
  obtain ⟨ε, hε, hε1, hεP⟩ := p.em_unr 0
  obtain ⟨a, h1, h2, h3⟩ := exists_idem_seq (V.l : O) ε hε
  obtain ⟨M, M', e1, e2, l1, l2⟩ := GlobalTheory.ActionLimit.exists_isEnd_of_limit C V O dd Y d I p a h1
  simp only [hρ] at l1 l2
  refine ⟨![M, M'], e1, e2, Fin.forall_fin_two.2 ⟨⟨ε, a, l1, hε, hε1, hεP, h2, h3⟩,
    star ε, fun m => star (a m), l2, ?_, fun t => ?_, fun x hx => ?_, fun m => ?_, fun m => ?_⟩⟩
  · obtain ⟨y, hy⟩ := hε
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · rw [p.em_conj, star_star]; exact hε1 t
  · obtain ⟨y, hy⟩ := hεP (star x) fun t => by rw [← p.em_conj]; exact hx t
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · obtain ⟨y, hy⟩ := h2 m
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · obtain ⟨y, hy⟩ := h3 m
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩

theorem exists_orth_proj : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o)), (∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' → ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0) → ∃ M : Orb → Fin 2 → Matrix (Fin dd) (Fin dd) C, (∀ o, IsEnd (Y.raw (p o)) V (M o 0) (M o 1) ∧ IsEnd (Y.raw (p o)) V (M o 1) (M o 0)) ∧ (∀ o g c, (M o g).mulVec ((p o).u g c) = (p o).u g c) ∧ (∀ o g o' g' c, (o, g) ≠ (o', g') → (M o g).mulVec ((p o').u g' c) = 0) ∧ ∀ o g v, ∃ b : I o g → C, (M o g).mulVec v = ∑ c, b c • (p o).u g c := by
  intro C _ _ V O _ _ dd Y d _ Orb I _ p hsep
  haveI := Y.algClosed
  obtain ⟨ρ, hρ1, hρ⟩ := exists_linHom Y.B.G Y.B.A
  have hint : ∀ x i j, V.Ge 0 (ρ x i j) := fun x i j => by rw [hρ1]; exact Y.intAct x i _
  choose M e1 e2 hM using fun o => exists_lim_pair Y (p o) ρ hρ
  have hs : ∀ o g (a a' : ZMod d), a ≠ a' → ∃ x, V.v ((p o).em g a x - (p o).em g a' x) = 0 :=
    fun o g a a' h => (p o).em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')
  refine ⟨M, fun o => ⟨e1 o, e2 o⟩, fun o g c => ?_, fun o g o' g' c hne => ?_, fun o g v => ?_⟩
  · obtain ⟨ε, a, hl, -, hε1, -, ha, ha0⟩ := hM o g
    have := hl.eig ((p o).em g ((p o).ty g c)) 1 (seq_one ha ha0 _ ((p o).em_int g _) (hε1 _)) ((p o).u g c)
      (fun x => by rw [← hρ, (p o).u_eig])
    rwa [one_smul] at this
  · obtain ⟨ε, a, hl, hε, hε1, hεP, ha, ha0⟩ := hM o g
    have hmm : V.MM ((p o').em g' ((p o').ty g' c) ε) := by
      by_contra hmm
      obtain ⟨t, ht⟩ := eq_em_of_not_mm ((p o).em g) ((p o).em_int g) ((p o).em_frob g) (hs o g) ε hε hε1 hεP _
        ((p o').em_int g' _) hmm
      obtain ⟨x, hx⟩ := hsep (o, g, t) (o', g', (p o').ty g' c) fun h =>
        hne (congrArg (fun z : Orb × Fin 2 × ZMod d => (z.1, z.2.1)) h)
      simp [ht] at hx
    have := hl.eig ((p o').em g' ((p o').ty g' c)) 0 (seq_zero ha ha0 _ ((p o').em_int g' _) hmm) ((p o').u g' c)
      (fun x => by rw [← hρ, (p o').u_eig])
    rwa [zero_smul] at this
  · obtain ⟨ε, a, hl, hε, hε1, hεP, ha, ha0⟩ := hM o g
    have := hl.range hint ((p o).em g) ((p o).em_int g) ((p o).em_frob g) (hs o g) ε hε hε1 hεP ha ha0
      (Submodule.span C (Set.range ((p o).u g))) (fun t w hw => by
        obtain ⟨b, -, hb⟩ := (p o).u_full g t w fun x => by rw [hρ, hw]
        exact (Submodule.mem_span_range_iff_exists_fun C).2 ⟨b, hb.symm⟩) v
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 this
    exact ⟨b, hb.symm⟩

end GlobalTheory.PlaceProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsRingHomValuationRingOfEmbOKStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_valuationRing_of_embOK : ∀ (T : CDVR) (C : Type) [Field C] [CharZero C] (V : VF C) (ι' : T.Fr →+* C), EmbOK T V ι' → ∃ j : T.V →+* V.RR, (∀ x, (j x : C) = ι' (algebraMap T.V T.Fr x)) ∧ ∀ x ∈ maximalIdeal T.V, V.MM (j x : C) := by
  first | exact @GlobalTheory.embOK_exists_ringHom | exact GlobalTheory.embOK_exists_ringHom | (intros; apply GlobalTheory.embOK_exists_ringHom <;> assumption)
end

