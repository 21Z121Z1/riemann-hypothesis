import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NatAbsDiscrMemDifferent
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0159
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0151
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0161
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangentsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_eigen_tangents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ), ∃ (r : ℕ) (e : Fin r → (epsAt x ⟶ t.G)), StableEig t x κ σ e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig | exact GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.EigStalk.exists_stableEig <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_label_bases_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ m : ℕ, 0 < m ∧ ∀ (s : CMType H ⊕ CMType H) (p : Cpt 𝔐.ξ), ∃ (b : Fin (labelRk D s) → 𝔐.Li) (π : Fin (labelRk D s) → Module.Dual Ω 𝔐.Li), (∀ i, flagStep Ω b i = flagStep Ω (Fl.b s) i) ∧ (𝔐.V s).IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ 𝔐.M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧ ∀ i, ∀ e ∈ 𝔐.M.lat p, (m : Ω) * π i e ∈ regAt 𝔐.ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich | exact GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich | (intros; apply GlobalTheory.CompanionTheory.Ar.Sandwich.lat_sandwich <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionExteriorValueStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_exterior_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) (S : Type) [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (R : Type) [CommRing R] (x : Sp R ⟶ Y.X) [IsOpenImmersion x] (φ₂ : R →+* Z.Ω) (e₁ : Fin D.p → (epsAt x ⟶ Y.t.G)) (e₂ : Fin D.q → (epsAt x ⟶ Y.t.G)) (f : R) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω) (B : Type) [CommRing B] [Algebra S B] (θ : R →+* B) (C₁ : Matrix (Fin D.p) (Fin D.p) B) (C₂ : Matrix (Fin D.q) (Fin D.q) B), IsLineFn U τ φ → Represents Y U τ Z.M a b φ → spMap φ₂ ≫ x = Z.ξ₀ ≫ Y.j → a = α • exteriorPower.ιMulti Z.Ω D.p b₁ → b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → φ₂ f = α / κ → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₁ i)) → (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G x (e₂ i)) → (∀ i, (Z.M.pt (b₁ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₁ i).left) → (∀ i, (Z.M.pt (b₂ i)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ₂) ≫ (e₂ i).left) → spMap θ ≫ x = spMap (algebraMap S B) ≫ zPt z ≫ Y.j → IsUnit C₁.det → IsUnit C₂.det → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₁ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u τ (k.cast hp.symm)) (C₁ i) V) → (∀ i, ∃ V : Sp (DualNumber B) ⟶ Xo.univ.t.G.left, Tied Y (spMap (algebraMap S B) ≫ zPt z) V (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e₂ i).left) ∧ Formalism.L2.Pj.IsCombAt (spMap (algebraMap S B) ≫ z.x) (fun k => spMap (Formalism.L2.Pj.dualMap (algebraMap S B)) ≫ z.u (ComplexEmbedding.conjugate τ) (k.cast hq.symm)) (C₂ i) V) → ∀ (F : Type) [Field F] (ψ : B →+* F) (y : Sp F ⟶ Xo.XF c), y = spMap ψ ≫ spMap (algebraMap S B) ≫ zPt z → Set.range y ⊆ U → ∀ (v : Vecs y D.p) (w : Vecs y D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap (ψ.comp (algebraMap S B))) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → φ F y v w * ψ C₂.det = ψ (θ f) * ψ C₁.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point | exact GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.function_of_frames_at_field_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTorsionUnramifiedPrime
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem htLattice_eq_dR_of_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → Nonempty (GenTors 𝔐 p) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q :=
  @PositivityTheory.Xgn.lattice_height_unit

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHolds
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

def powChar {R : Type} [CommRing R] (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) :
    Multiplicative (ZMod m) →* Rˣ where
  toFun k := ζ ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hζ).symm

theorem powChar_apply {R : Type} [CommRing R] (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (k : ZMod m) :
    powChar m ζ hζ (Multiplicative.ofAdd k) = ζ ^ k.val := rfl

def liftSurj {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T) (hπ : Function.Surjective π)
    (f : G →* H) (hf : ∀ z, π z = 1 → f z = 1) : T →* H :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨f, fun z hz => (MonoidHom.mem_ker).2 (hf z ((MonoidHom.mem_ker).1 hz))⟩

theorem liftSurj_apply {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T)
    (hπ : Function.Surjective π) (f : G →* H) (hf : ∀ z, π z = 1 → f z = 1) (z : G) :
    liftSurj π hπ f hf (π z) = f z :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

theorem hom_ext_of_surj {G T H : Type} [Group G] [Group T] [Group H] (π : G →* T)
    (hπ : Function.Surjective π) (χ χ' : T →* H) (h : ∀ z, χ (π z) = χ' (π z)) : χ = χ' :=
  MonoidHom.ext fun t => by
    obtain ⟨z, rfl⟩ := hπ t
    exact h z

variable {R : Type} [CommRing R] {E : Type} [Field E] [NumberField E] {N : ℕ} {T : Type} [CommGroup T]

def charOf (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m) (y : Fin N → 𝓞 E) : T →* Rˣ :=
  liftSurj π hπ ((powChar m ζ hζ).comp (e y).toMultiplicative) (fun z hz => by
    obtain ⟨z', hz'⟩ := (hker (Multiplicative.toAdd z)).1 hz
    have h0 : e y (Multiplicative.toAdd z) = 0 := by
      rw [hz', map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    show powChar m ζ hζ (Multiplicative.ofAdd (e y (Multiplicative.toAdd z))) = 1
    rw [h0, ofAdd_zero, map_one])

theorem charOf_apply (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m) (y z : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e y (π (Multiplicative.ofAdd z)) = ζ ^ (e y z).val :=
  liftSurj_apply _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

variable {R : Type} [CommRing R] {E : Type} [Field E] [NumberField E] {N : ℕ} {T : Type} [CommGroup T]

section chars
variable (m : ℕ) [NeZero m] (ζ : Rˣ) (hζ : ζ ^ m = 1) (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (hker : ∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = m • y')
    (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod m)

omit [NeZero m] in
theorem charOf_eq_iff (π : Multiplicative (Fin N → 𝓞 E) →* T)
    (hπ : Function.Surjective π) (χ χ' : T →* Rˣ) (h : ∀ z, χ (π (Multiplicative.ofAdd z)) = χ' (π (Multiplicative.ofAdd z))) :
    χ = χ' :=
  hom_ext_of_surj π hπ χ χ' fun z => h (Multiplicative.toAdd z)

theorem charOf_add (y y' : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e (y + y') = charOf m ζ hζ π hπ hker e y * charOf m ζ hζ π hπ hker e y' :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.mul_apply, charOf_apply, charOf_apply, charOf_apply, ← powChar_apply m ζ hζ,
      ← powChar_apply m ζ hζ, ← powChar_apply m ζ hζ, map_add, AddMonoidHom.add_apply, ofAdd_add, map_mul]

theorem charOf_zero : charOf m ζ hζ π hπ hker e 0 = 1 :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.one_apply, charOf_apply, ← powChar_apply m ζ hζ, map_zero, AddMonoidHom.zero_apply,
      ofAdd_zero, map_one]

theorem charOf_neg (y : Fin N → 𝓞 E) :
    charOf m ζ hζ π hπ hker e (-y) = (charOf m ζ hζ π hπ hker e y)⁻¹ :=
  charOf_eq_iff π hπ _ _ fun z => by
    rw [MonoidHom.inv_apply, charOf_apply, charOf_apply, ← powChar_apply m ζ hζ,
      ← powChar_apply m ζ hζ, map_neg, AddMonoidHom.neg_apply, ofAdd_neg, map_inv]

def mulMap (b : 𝓞 E) : T →* T :=
  liftSurj π hπ (π.comp (DistribMulAction.toAddMonoidHom (Fin N → 𝓞 E) b).toMultiplicative) (fun z hz => by
    obtain ⟨z', hz'⟩ := (hker (Multiplicative.toAdd z)).1 hz
    show π (Multiplicative.ofAdd (b • Multiplicative.toAdd z)) = 1
    rw [hker, hz', smul_comm]
    exact ⟨_, rfl⟩)

theorem mulMap_apply (b : 𝓞 E) (z : Fin N → 𝓞 E) :
    mulMap m π hπ hker b (π (Multiplicative.ofAdd z)) = π (Multiplicative.ofAdd (b • z)) :=
  liftSurj_apply _ _ _ _ _

end chars

def dualAct {L : Type} [AddCommGroup L] [Module R L] (ρ : 𝓞 E →+* Module.End R L) (σ : 𝓞 E ≃+* 𝓞 E) :
    𝓞 E →+* Module.End R (Module.Dual R L) where
  toFun a := (ρ (σ a)).dualMap
  map_one' := by ext w l; simp
  map_mul' a b := by
    rw [mul_comm a b]
    ext w l
    simp [Module.End.mul_apply]
  map_zero' := by ext w l; simp
  map_add' a b := by ext w l; simp

theorem dualAct_apply {L : Type} [AddCommGroup L] [Module R L] (ρ : 𝓞 E →+* Module.End R L) (σ : 𝓞 E ≃+* 𝓞 E)
    (a : 𝓞 E) (w : Module.Dual R L) : dualAct ρ σ a w = w ∘ₗ ρ (σ a) := rfl

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx

namespace GlobalTheory.CompanionTheory.Ar.BT.ChartEx

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField

theorem htChartExists : HTChartExists := by
  intro R K _ _ _ _ _ _ _ _ E _ _ c p n N _ T _ _ Γ S G _ _ x i hTor hSm act hmon L _ _ M ρ hρ Ω _ _ _ _ j hj
    π hπ hker hact ζ hζ e halt hadj hsurj hinj
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hpn : ((p ^ n : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI : Smooth G.hom := hSm
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.T.lie_model_finite_base_change S G R x L M

  have hex : ∀ χ : T →* Rˣ, ∃ w, Γ.IsHT i M (p ^ n) χ w := fun χ =>
    GlobalTheory.T.exists_hodge_tate_functional R T Γ S G x (p ^ n) i hTor hSm L M χ
  have hadd : ∀ (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w → Γ.IsHT i M (p ^ n) χ' w' →
      Γ.IsHT i M (p ^ n) (χ * χ') (w + w') := fun χ χ' w w' =>
    GlobalTheory.T.hodge_tate_functional_mul R T Γ S G x (p ^ n) i hTor L M χ χ' w w'
  have huniq : ∀ (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w →
      (Γ.IsHT i M (p ^ n) χ w' ↔ ∃ u : Module.Dual R L, w' = w + (p ^ n) • u) := fun χ w w' =>
    GlobalTheory.T.hodge_tate_functional_unique_mod_smul R T Γ S G x (p ^ n) i hTor hSm hpn L M χ w w'
  have hzero : Γ.IsHT i M (p ^ n) 1 0 := by
    obtain ⟨w, hw⟩ := hex 1
    have h2 := hadd 1 1 w w hw hw
    rw [_root_.mul_one] at h2
    obtain ⟨u, hu⟩ := (huniq 1 w (w + w) hw).1 h2
    refine (huniq 1 w 0 hw).2 ⟨-u, ?_⟩
    have : w = (p ^ n) • u := add_left_cancel hu
    rw [smul_neg, this, add_neg_cancel]
  have hneg : ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M (p ^ n) χ w → Γ.IsHT i M (p ^ n) χ⁻¹ (-w) := by
    intro χ w hw
    obtain ⟨w', hw'⟩ := hex χ⁻¹
    have h2 := hadd χ χ⁻¹ w w' hw hw'
    rw [_root_.mul_inv_cancel] at h2
    obtain ⟨u, hu⟩ := (huniq 1 0 (w + w') hzero).1 h2
    refine (huniq χ⁻¹ w' (-w) hw').2 ⟨-u, ?_⟩
    rw [zero_add] at hu
    rw [smul_neg, ← hu]
    abel

  let χ := charOf (p ^ n) ζ hζ π hπ hker e
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Free.ChooseBasisIndex ℤ (Fin N → 𝓞 E)) ℤ (Fin N → 𝓞 E)) :=
    ⟨Module.Free.chooseBasis ℤ (Fin N → 𝓞 E)⟩
  choose wb hwb using fun k => hex (χ (b k))
  let h : (Fin N → 𝓞 E) →+ Module.Dual R L := (b.constr ℤ wb).toAddMonoidHom
  have hh : ∀ y, Γ.IsHT i M (p ^ n) (χ y) (h y) := by
    intro y
    have hy : y ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      rw [Submodule.mem_toAddSubgroup, b.span_eq]; exact Submodule.mem_top
    rw [Submodule.span_int_eq_addSubgroupClosure] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      have : h (b k) = wb k := by simp [h, Module.Basis.constr_basis]
      rw [this]; exact hwb k
    | zero => rw [map_zero, show χ 0 = 1 from charOf_zero _ _ _ _ _ _ _]; exact hzero
    | add y y' _ _ h1 h2 =>
      rw [map_add, show χ (y + y') = χ y * χ y' from charOf_add _ _ _ _ _ _ _ y y']; exact hadd _ _ _ _ h1 h2
    | neg y _ h1 => rw [map_neg, show χ (-y) = (χ y)⁻¹ from charOf_neg _ _ _ _ _ _ _ y]; exact hneg _ _ h1

  have hlin : ∀ (a : 𝓞 E) y, ∃ u, h (a • y) = dualAct ρ (RingOfIntegers.mapRingEquiv c) a (h y) + (p ^ n) • u := by
    intro a y
    have hαc : χ (a • y) = (χ y).comp (mulMap (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a)) :=
      charOf_eq_iff π hπ _ _ fun z => by
        rw [MonoidHom.comp_apply, mulMap_apply, charOf_apply, charOf_apply, hadj]
    have hαpt : ∀ t, (Γ.pt (mulMap (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a) t)).left ≫ i =
        (Γ.pt t).left ≫ i ≫ (act (RingOfIntegers.mapRingEquiv c a)).left := by
      intro t
      obtain ⟨z, rfl⟩ := hπ t
      have := mulMap_apply (p ^ n) π hπ hker (RingOfIntegers.mapRingEquiv c a) (Multiplicative.toAdd z)
      rw [ofAdd_toAdd] at this
      rw [this]
      exact hact _ _
    haveI := hmon (RingOfIntegers.mapRingEquiv c a)
    have h1 : Γ.IsHT i M (p ^ n) (χ (a • y)) (dualAct ρ (RingOfIntegers.mapRingEquiv c) a (h y)) := by
      rw [hαc, dualAct_apply]
      exact GlobalTheory.T.hodge_tate_functional_endomorphism R T Γ S G x (p ^ n) i hTor L M (act (RingOfIntegers.mapRingEquiv c a)) _
        (ρ (RingOfIntegers.mapRingEquiv c a)) hαpt (hρ _) (χ y) (h y) (hh y)
    obtain ⟨u, hu⟩ := (huniq _ _ _ (hh (a • y))).1 h1
    refine ⟨-u, ?_⟩
    rw [hu, smul_neg, add_neg_cancel_right]
  obtain ⟨D, hDom, hDe, hDh, hDρ⟩ := GlobalTheory.T.hodge_tate_lattice_base_change_pairing R K E c p n N (Module.Dual R L) Ω j hj
    (dualAct ρ (RingOfIntegers.mapRingEquiv c)) e h halt hadj hsurj hinj hlin
  refine ⟨D, hDe, hDom, fun a w => ?_, fun y => ⟨χ y, h y, fun z => ?_, hDh y, hh y⟩⟩
  · rw [hDρ]; rfl
  · rw [hDe]; exact charOf_apply _ _ _ _ _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.BT.ChartEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareGeneric
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem exists_valPoint {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (W : ValuationSubring Ω') (i : Ω →+* Ω') (q : Cpt ξ) (hinj : Function.Injective (genMap ξ q))
    (h : DomBy W.toSubring i ξ q) :
    ∃ z : Sp W ⟶ X, spMap W.subtype ≫ z = spMap i ≫ ξ ∧ z (IsLocalRing.closedPoint W) = q.1 := by
  obtain ⟨h1, h2⟩ := h
  let φ : X.presheaf.stalk q.1 →+* W :=
    (i.comp (genMap ξ q)).codRestrict W.toSubring (fun a => h1 _ ⟨a, rfl⟩)
  have hφ : ∀ a, ((φ a : W) : Ω') = i (genMap ξ q a) := fun _ => rfl
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    have hne : genMap ξ q a ≠ 0 := by
      intro h0
      have : φ a = 0 := Subtype.ext (by rw [hφ, h0, map_zero]; rfl)
      rw [this] at ha
      exact not_isUnit_zero ha
    have hinv : (i (genMap ξ q a))⁻¹ ∈ W.toSubring := by
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hb' : i (genMap ξ q a) * (b : Ω') = 1 := by
        have := congrArg (fun x : W => (x : Ω')) hb
        simpa [hφ] using this
      rw [inv_eq_of_mul_eq_one_right hb']
      exact b.2
    obtain ⟨b, hb⟩ := h2 _ ⟨a, rfl⟩ hne hinv
    refine IsUnit.of_mul_eq_one b (hinj ?_)
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  let z : Sp W ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1
  refine ⟨z, ?_, ?_⟩
  · have e : CommRingCat.ofHom φ ≫ CommRingCat.ofHom W.subtype =
        X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
      ext a
      rfl
    have e2 : spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) =
        spMap i ≫ Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
      simp only [spMap, ← Spec.map_comp]
      rw [e]
      rfl
    show spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1 = _
    rw [← Category.assoc, e2]
    simp only [Category.assoc]
    have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
    have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have e5 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) ≫
        X.fromSpecStalk q.1 = ξ :=
      (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4
    exact congrArg (spMap i ≫ ·) e5
  · have : IsLocalHom (CommRingCat.ofHom φ).hom := hloc
    change X.fromSpecStalk q.1 (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint W)) = q.1
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem isSeparated_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str R N) := by
    unfold PSpace.str
    infer_instance
  infer_instance

theorem image_eq_of_domBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∀ (W : ValuationSubring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), DomBy W.toSubring (RingHom.id Ω) 𝔐.ξ q → DomBy W.toSubring i 𝔐₀.ξ q₀ → 𝔐.f q.1 = 𝔐₀.f q₀.1 := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i hξ W q q₀ hq hq₀
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W (RingHom.id Ω) q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐₀.ξ W i q₀ (𝔐₀.tie.gen.inj q₀) hq₀
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐₀.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp, hξ]
    simp only [Category.assoc]
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐₀.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐₀.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐₀.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscRatioGrowthStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_disc_ratio_growth : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc | exact GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PoleDisc.pole_disc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameOpenConditionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_open_condition : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E), M.lat.IsFrameAt b p → Submodule.span Ω (Set.range b) = ⊤ ∧ ∃ N : X.Opens, p.1 ∈ N ∧ ∀ q : Cpt ξ, q.1 ∈ N → M.lat.IsFrameAt b q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd | exact GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd | (intros; apply GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDescendsBaseChange
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul]
  · simp [dualMap, epsMul, mul_comm]

def epsBase (c : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, dualMap_comp_algebraMap])

def ptBase (c : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap c ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap c) rfl

theorem isTanAt_base (G : Over S) [GrpObj G] (c : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap c ≫ x) (epsBase c x ≫ v) := by
  have h1 : (ptBase c x ≫ (1 : Over.mk x ⟶ G)) = 1 := MonObj.comp_one _
  have h2 : spMap c ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap c ≫ x) ⟶ G).left := by
    rw [← h1]; rfl
  unfold IsTanAt at hv ⊢
  rw [← h2, ← hv]
  change Spec.map _ ≫ spMap (dualMap c) ≫ v.left = spMap c ≫ Spec.map _ ≫ v.left
  simp only [spMap]
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, fst_comp_dualMap]

theorem exists_isBaseChange (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type)
    [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E']
    [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'),
      IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  obtain ⟨E, iA, iM, ⟨M⟩⟩ := lieModel_exists S G R x
  have hex : ∀ e, ∃ e', M'.pt e' = epsBase (algebraMap R R') x ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base G _ x _ (M.tan e))
  choose f hf using hex
  have hleft : ∀ e, (M'.pt (f e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := fun e => by
    rw [hf e]; rfl
  let j : E →ₗ[R] E' :=
    { toFun := f
      map_add' := fun a b => M'.inj (by
        rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul])
      map_smul' := fun r a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, ← algebraMap_smul R' r (f a), M'.smul, hleft, hleft, M.smul]
        simp only [spMap]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, dualMap_comp_epsMul])) }
  refine ⟨E, iA, iM, M, j, GlobalTheory.T.lie_model_isBaseChange S G R R' x E E' M M' j fun e => ?_, hleft⟩
  change (M'.pt (f e)).left ≫ 𝟙 G.left = _
  rw [Category.comp_id, hleft]

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteGeneratingValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_finite_generating_values : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_free_over_local_ring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth | exact GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth <;> assumption)
end

