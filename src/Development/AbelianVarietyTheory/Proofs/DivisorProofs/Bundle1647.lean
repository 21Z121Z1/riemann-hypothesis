import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismFiniteOfGeometricFibresStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_endomorphism_finite_of_geometric_fibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  first | (exact @GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres) | (exact GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres) | (intros; apply GlobalTheory.AbEnd.isFinite_of_isFinite_geomFibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_globalOneForms_primitive : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → PrimF A := by
  first | exact @GlobalTheory.AbCoh.primF_of_abelian | exact GlobalTheory.AbCoh.primF_of_abelian | (intros; apply GlobalTheory.AbCoh.primF_of_abelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometricStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_torsionPoint_trivial_of_geometric : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (T : Over S) (x : T ⟶ A) (c : ℕ), IsUnit (c : Γ(T.left, ⊤)) → x ^ c = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S) (g : Over.mk z ⟶ T), g ≫ x = 1) → x = 1 := by
  first | (exact @GlobalTheory.TorsionRigid.eq_one_of_geometric) | (exact GlobalTheory.TorsionRigid.eq_one_of_geometric) | (intros; apply GlobalTheory.TorsionRigid.eq_one_of_geometric  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
section
noncomputable section

namespace GlobalTheory.LevelActionOfLifts

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem levR_congr {f g k : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : ∀ a, f a - g a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR (f, k) y y' ↔ levR (g, k) y y' := by
  have e : ∀ a, Xo.univ.eta (f a) = Xo.univ.eta (g a) := fun a => GlobalTheory.LevelActionLaws.eta_congr Xo (h a)
  unfold levR IsLevMove
  simp only [e]

def modHalf (l : Level H) (f : Dw.La →ₗ[𝓞 E] Dw.La) : Module.End (𝓞 E) (LaMod Dw l) :=
  Submodule.mapQ _ _ f (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

end General

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem actLev_of_lifts (Xo : Moduli Dw l) (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
    (h1 : ∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La))
    (hm : ∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) := by
  let φ : G →* Module.End (𝓞 D.host.E) (LaMod Dw l) :=
    { toFun := fun g => modHalf l (lev g)
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Submodule.Quotient.eq _).2 (h1 a)
      map_mul' := fun g h => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        exact (Submodule.Quotient.eq _).2 (hm g h a) }
  let ψ : G →* (LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (𝓞 D.host.E) (LaMod Dw l)).toMonoidHom.comp φ.toHomUnits
  have key : ∀ (g : G) {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S),
      levActR (Xo := Xo) (c := c) (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) g y y' ↔
        levActR (Xo := Xo) (c := c) (GlobalTheory.FormTies.levFull Dw l) (ψ g) y y' := by
    intro g S _ _ y y'
    refine levR_congr (fun a => (Submodule.Quotient.eq _).1 ?_) y y'
    exact (liftLa_spec (ψ g) a).symm
  have L := GlobalTheory.FullLevelAction.actLaws_levFull Xo c hpq hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨y', h⟩ := L.total (ψ g) S y
    exact ⟨y', (key g y y').2 h⟩
  · intro g S _ _ y y' y'' h h'
    exact L.func (ψ g) S y y' y'' ((key _ _ _).1 h) ((key _ _ _).1 h')
  · intro S _ _ y
    refine (key 1 y y).2 ?_
    rw [map_one]
    exact L.one S y
  · intro g h S _ _ y y' y'' a b
    refine (key _ _ _).2 ?_
    rw [map_mul]
    exact L.mul _ _ S y y' y'' ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S T _ _ _ _ φ y y' z z' m a b
    exact L.nat (ψ g) S T φ y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)
  · intro g S _ _ t y y' z z' m a b
    exact L.bor (ψ g) S t y y' z z' m ((key _ _ _).1 a) ((key _ _ _).1 b)

theorem actLev_of_lifts_of_eq_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La)), 1 ≤ Dw.p + Dw.q → l.A = 1 → (∀ a, lev 1 a - a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → (∀ g h a, lev (g * h) a - lev g (lev h a) ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) → ActLev (Xo := Xo) c (fun g => (lev g, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) := by
  intro D H Dw l Xo c G _ lev hpq hA h1 hm
  exact actLev_of_lifts Xo c lev hpq (by rw [hA]; exact Nat.coprime_one_left _) h1 hm

end GlobalTheory.LevelActionOfLifts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
section
open NumberField MeasureTheory

namespace GlobalTheory.WeilM

theorem schA_memLp_two : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  intro μ hμ Φ hΦ
  obtain ⟨n, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  exact memLp_finset_sum' _ fun i _ => GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ (f i) (hg i)

end GlobalTheory.WeilM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapMemMaximalIdealIff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem algebraMap_mem_maximalIdeal_iff (c : k) :
    algebraMap k S c ∈ maximalIdeal S ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    exact h ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k S))
  · rintro rfl
    simp

theorem residue_eq {π : S → k} (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (s : S) (c : k) (h : s - algebraMap k S c ∈ maximalIdeal S) : π s = c := by
  have hm : algebraMap k S (π s - c) ∈ maximalIdeal S := by
    have := sub_mem h (hπ s)
    rw [map_sub]; convert this using 1; ring
  rw [algebraMap_mem_maximalIdeal_iff] at hm
  exact sub_eq_zero.mp hm

def tangentHom (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) :
    S →ₐ[k] DualNumber k where
  toFun s := TrivSqZeroExt.inl (π s) + TrivSqZeroExt.inr (f s)
  map_one' := by
    have : π 1 = 1 := residue_eq hπ 1 1 (by simp)
    ext <;> simp [this, hf1]
  map_mul' s t := by
    have hm : π (s * t) = π s * π t := residue_eq hπ _ _ (by
      rw [map_mul]
      convert add_mem (Ideal.mul_mem_right t _ (hπ s)) (Ideal.mul_mem_left _ (algebraMap k S (π s)) (hπ t))
        using 1
      ring)
    have hfa : ∀ c, f (algebraMap k S c) = 0 := by
      intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    have e : s * t = algebraMap k S (π s * π t) + π s • (t - algebraMap k S (π t)) +
        π t • (s - algebraMap k S (π s)) +
        (s - algebraMap k S (π s)) * (t - algebraMap k S (π t)) := by
      simp only [Algebra.smul_def, map_mul]; ring
    have hf : f (s * t) = π s * f t + π t * f s := by
      have huv := hf2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hπ s) (hπ t))
      rw [e, map_add, map_add, map_add, map_smul, map_smul, huv, map_sub, map_sub, hfa, hfa, hfa]
      simp
    ext <;> simp [hm, hf] <;> ring
  map_zero' := by
    have : π 0 = 0 := residue_eq hπ 0 0 (by simp)
    ext <;> simp [this]
  map_add' s t := by
    have : π (s + t) = π s + π t := residue_eq hπ _ _ (by
      rw [map_add]; convert add_mem (hπ s) (hπ t) using 1; ring)
    ext <;> simp [this]
  commutes' c := by
    have : π (algebraMap k S c) = c := residue_eq hπ _ _ (by simp)
    have h0 : f (algebraMap k S c) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    ext <;> simp [this, h0, TrivSqZeroExt.algebraMap_eq_inl]

theorem tangentHom_snd (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) (s : S) :
    (tangentHom π hπ f hf1 hf2 s).snd = f s := by
  simp [tangentHom]

theorem epsScaleR_snd (c : k) (x : DualNumber k) : (epsScaleR c x).snd = c * x.snd := by
  simp [epsScaleR]

end GlobalTheory.LocalTangent

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem exists_form {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S)
    (h : ∀ c : k, a - c • b ∉ maximalIdeal S ^ 2) :
    ∃ f : S →ₗ[k] k, f 1 = 0 ∧ (∀ y ∈ maximalIdeal S ^ 2, f y = 0) ∧ f b = 0 ∧ f a = 1 := by
  let P : Submodule k S := Submodule.span k {1, b} ⊔ (maximalIdeal S ^ 2).restrictScalars k
  have haP : a ∉ P := by
    intro hP
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hP
    obtain ⟨l, r, rfl⟩ := Submodule.mem_span_pair.mp hy
    have hz2 : z ∈ maximalIdeal S ^ 2 := hz
    have hz' : z ∈ maximalIdeal S := Ideal.pow_le_self two_ne_zero hz2
    have hl : l = 0 := by
      rw [← algebraMap_mem_maximalIdeal_iff (S := S)]
      have e : algebraMap k S l = a - r • b - z := by
        rw [← hyz, Algebra.algebraMap_eq_smul_one]; abel
      rw [e]
      exact sub_mem (sub_mem ha (Submodule.smul_of_tower_mem _ r hb)) hz'
    apply h r
    have e : a - r • b = z := by rw [← hyz, hl]; simp
    rw [e]; exact hz2
  obtain ⟨g, hga, hgP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem haP (by infer_instance)
  have hg0 : ∀ y ∈ P, g y = 0 := fun y hy => by
    have : g y ∈ P.map g := Submodule.mem_map_of_mem hy
    rw [hgP] at this; exact (Submodule.mem_bot k).mp this
  refine ⟨(g a)⁻¹ • g, ?_, ?_, ?_, ?_⟩
  · simp [hg0 1 (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · intro y hy
    simp [hg0 y (Submodule.mem_sup_right hy)]
  · simp [hg0 b (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · simp [hga]

theorem pair_dependent
    (h1 : ∀ a : S, ∃ c : k, a - algebraMap k S c ∈ maximalIdeal S)
    (h3 : ∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k))
    {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S) :
    ∃ c : k, a - c • b ∈ maximalIdeal S ^ 2 ∨ b - c • a ∈ maximalIdeal S ^ 2 := by
  by_contra hne
  push_neg at hne
  choose π hπ using h1
  obtain ⟨f₁, h11, h12, h13, h14⟩ := exists_form ha hb (fun c => (hne c).1)
  obtain ⟨f₂, h21, h22, h23, h24⟩ := exists_form hb ha (fun c => (hne c).2)
  obtain ⟨c, hc | hc⟩ := h3 (tangentHom π hπ f₁ h11 h12) (tangentHom π hπ f₂ h21 h22)
  · have := congrArg (fun φ : S →+* DualNumber k => (φ a).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h14, h23, mul_zero] at this
    exact one_ne_zero this
  · have := congrArg (fun φ : S →+* DualNumber k => (φ b).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h24, h13, mul_zero] at this
    exact one_ne_zero this

theorem maximalIdeal_isPrincipal : ∀ (k : Type) [Field k] (S : Type) [CommRing S] [IsLocalRing S] [Algebra k S],
    (∀ a : S, ∃ c : k, a - algebraMap k S c ∈ IsLocalRing.maximalIdeal S) →
    IsNilpotent (IsLocalRing.maximalIdeal S) →
    (∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k)) →
    (IsLocalRing.maximalIdeal S).IsPrincipal := by
  intro k _ S _ _ _ h1 hnil h3
  set m := maximalIdeal S with hm
  have hx : ∃ x ∈ m, m ≤ Ideal.span {x} ⊔ m ^ 2 := by
    by_cases hle : m ≤ m ^ 2
    · exact ⟨0, zero_mem _, le_sup_of_le_right hle⟩
    · obtain ⟨x, hxm, hx2⟩ := Set.not_subset.mp hle
      refine ⟨x, hxm, fun a ha => ?_⟩
      have key : ∃ c : k, a - c • x ∈ m ^ 2 := by
        obtain ⟨c, hc | hc⟩ := pair_dependent h1 h3 ha hxm
        · exact ⟨c, hc⟩
        · have hc0 : c ≠ 0 := by
            rintro rfl; apply hx2; simpa using hc
          refine ⟨c⁻¹, ?_⟩
          have e : a - c⁻¹ • x = (-c⁻¹) • (x - c • a) := by
            rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc0, neg_smul, neg_smul, one_smul]; abel
          rw [e]; exact Submodule.smul_of_tower_mem _ _ hc
      obtain ⟨c, hc⟩ := key
      have e : a = c • x + (a - c • x) := by abel
      rw [e]
      refine Submodule.add_mem_sup ?_ hc
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  obtain ⟨x, hxm, hle⟩ := hx
  set I := Ideal.span {x}
  have hstep : ∀ n : ℕ, m ≤ I ⊔ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc m ≤ I ⊔ m ^ 2 := hle
        _ = I ⊔ m * m := by rw [pow_two]
        _ ≤ I ⊔ m * (I ⊔ m ^ (n + 1)) := sup_le_sup_left (Ideal.mul_mono_right ih) _
        _ = I ⊔ (m * I ⊔ m ^ (n + 1 + 1)) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ I ⊔ m ^ (n + 1 + 1) := sup_le (le_sup_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
  obtain ⟨n, hn⟩ := hnil
  have hmI : m ≤ I := by
    have := hstep n
    rwa [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, sup_bot_eq] at this
  have hIm : I ≤ m := (Ideal.span_singleton_le_iff_mem _).mpr hxm
  exact ⟨⟨x, le_antisymm hmI hIm⟩⟩

end GlobalTheory.LocalTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDbarChernFormOfGramMatrixEqZeroStatement
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antiholomorphicDbar_chernFormOfGramMatrix_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, dbarAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  first | exact @GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt | exact GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt | (intros; apply GlobalTheory.CxForm.ChernDbar.dbarAt_chernAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchSchwartzL2BoundedIntertwinerContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

theorem realcont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)))
    (A : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ) (C : ℝ≥0∞), C ≠ ⊤ →
      (∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) →
      (∀ v (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ), ⇑f' = GlobalTheory.WeilAdm.schrInf D.host.F ψ v ⇑f →
        ⇑(A f') = GlobalTheory.WeilAdm.schrInf D.host.F ψ (L v) ⇑(A f)) →
      Continuous A := by
  intro D ps hψ κ _ L A C hC hA hI
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.T.standardAddChar_archimedean_exp_realLinear D ps θ hψ hθ
  have hnd : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 := by
    intro a ha
    have ha' : (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a ≠ 0 := by
      simpa using ha
    obtain ⟨b, hb⟩ := GlobalTheory.T.realTrace_archimedeanEmbeddings_nondegenerate D θ hθ _ ha'
    refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F b, ?_⟩
    rw [hβ2, map_mul, RingEquiv.symm_apply_apply]
    simpa using hb
  obtain ⟨n, Q, P, hQP⟩ := GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard D.host.F ps β hβ1 hnd κ
  obtain ⟨c, hc⟩ := GlobalTheory.T.lintegral_sq_comp_continuousLinearEquiv_mixedSpace D.host.F κ n Q
  let CQ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q
  let CQi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q.symm
  have hCQ : ∀ f, ⇑(CQ f) = ⇑f ∘ ⇑Q := fun f => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q f
  have hCQi : ∀ g, ⇑(CQi g) = ⇑g ∘ ⇑Q.symm := fun g => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q.symm g
  have hQQ : ∀ f, CQi (CQ f) = f := fun f => by
    ext z; rw [hCQi, hCQ]; simp
  have hQQ' : ∀ g, CQ (CQi g) = g := fun g => by
    ext z; rw [hCQ, hCQi]; simp
  let A' : GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := CQ.toLinearMap ∘ₗ A ∘ₗ CQi.toLinearMap
  have hA'apply : ∀ g, A' g = CQ (A (CQi g)) := fun g => rfl
  let L' : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := P.trans (L.trans P.symm)
  have hbound : ∀ g, ∫⁻ x, ‖A' g x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    intro g
    have e1 : ∫⁻ x, ‖A' g x‖ₑ ^ 2 = c * ∫⁻ z, ‖A (CQi g) z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hA'apply, hCQ, Function.comp_apply]
    have e2 : ∫⁻ x, ‖g x‖ₑ ^ 2 = c * ∫⁻ z, ‖CQi g z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hCQi, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [e1, e2, ← mul_assoc, mul_comm C c, mul_assoc]
    exact mul_le_mul' le_rfl (hA _)
  have hint : ∀ w (g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑g →
      ⇑(A' g') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := by
    intro w g g' hg
    have h1 : ⇑(CQi g') = schrInf D.host.F ps (P w) ⇑(CQi g) := by
      have := congrArg (fun u => u ∘ ⇑Q.symm) (hQP w ⇑(CQi g))
      simp only [Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id] at this
      rw [this, hCQi, hg, ← hCQ, hQQ']
    have h2 := hI (P w) (CQi g) (CQi g') h1
    have hL' : P (L' w) = L (P w) := P.apply_symm_apply _
    have h3 : ⇑(A (CQi g')) = schrInf D.host.F ps (P (L' w)) ⇑(A (CQi g)) := by
      rw [h2]
      exact congrArg (fun v => schrInf D.host.F ps v ⇑(A (CQi g))) hL'.symm
    calc ⇑(A' g') = ⇑(A (CQi g')) ∘ ⇑Q := hCQ _
      _ = schrInf D.host.F ps (P (L' w)) ⇑(A (CQi g)) ∘ ⇑Q := congrArg (· ∘ ⇑Q) h3
      _ = GlobalTheory.RealWeil.rhoFun (L' w) (⇑(A (CQi g)) ∘ ⇑Q) := hQP _ _
      _ = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := congrArg (GlobalTheory.RealWeil.rhoFun (L' w)) (hCQ _).symm
  have hcont : Continuous A' :=
    GlobalTheory.T.continuous_of_lie_intertwine_l2 (Fin n) L' A' C hC hbound (GlobalTheory.T.derived_action_intertwines_of_group (Fin n) L'.toLinearMap A' C hC hbound hint)
  have hAeq : ⇑A = fun f => CQi (A' (CQ f)) := by
    funext f
    rw [hA'apply, hQQ, hQQ]
  rw [hAeq]
  exact CQi.continuous.comp (hcont.comp CQ.continuous)

end GlobalTheory.WeilAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLTameOfFinitenessAtRankStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_GL_tame_of_finiteness_at_rank : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), (∀ (L' : Subgroup (GL (Fin n) (Af E))), IsOpen (L' : Set (GL (Fin n) (Af E))) → ∀ W' : Submodule ℂ (Kinf E n → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E n) → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E n L' W' X' N'))) → ∀ φ : Sm E n, IsAutForm φ → φ ∈ GlobalTheory.AutGrowth.tame E n := by
  first | exact @GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank | exact GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank | (intros; apply GlobalTheory.AutGrowth.RankLocal.tame_of_autForm_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLUniformModerateGrowth
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem GlobalTheory.AutGrowth.uniform_growth_of_autForm : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E]
    [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∃ N : ℕ, ∀ l : List (Lie E a),
    ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod φ).1 (infGL E a y)‖ ≤ C * height y ^ N := by
  intro hP E _ _ _ a φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨C, N, hC⟩ := hφ.growth 1
  simp only [one_mul] at hC
  obtain ⟨α, hα, hconv⟩ := GlobalTheory.T.automorphicForm_eq_own_realLieSmoothing hP E a ν φ hφ
  refine ⟨N, fun l => ?_⟩
  obtain ⟨β, hβ, hw⟩ := GlobalTheory.T.exists_test_word_eq_smoothing E a ν α hα φ hconv l
  obtain ⟨C', hC'⟩ := GlobalTheory.T.exists_smoothing_norm_le_height_pow E a ν β hβ φ.1 C N hC
  exact ⟨C', fun y => by rw [hw]; exact hC' y⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelRowsEqDimensionAll
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR

namespace GlobalTheory.Fc.Ind

theorem base_level_rows_eq_dimension : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Part D O c), BaseRankDimension D O c b := by
  intro D O c b
  have h1 : D.what₂.D0 = b.P.S0.D := GlobalTheory.rowSide_card_eq_of_coord O.ex.p0.s D.what₂.onb0 b.P.I.eRR0
  have key : ∀ (Z Z' : DefSub b.P.A3.fam3.amb3) (S : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z))
      (S' : IndefData (b.P.A3.side3 b.P.P0 b.P.ψ0 Z')), Z = Z' → HEq S S' → S.D = S'.D := by
    intro Z Z' S S' h h'
    subst h
    cases eq_of_heq h'
    rfl
  have h2 := key _ _ _ _ b.B.Q.zs b.B.Q.s0
  have h3 := b.B.Q.zs
  unfold BaseRankDimension
  rw [h1, ← h2, ← h3]
  rfl

end GlobalTheory.Fc.Ind
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteLocallyFreeRepresentablePropeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertScheme_finite_locallyFree_representable_proper : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbertSch.main) | (exact GlobalTheory.HilbertSch.main) | (intros; apply GlobalTheory.HilbertSch.main <;> assumption)
end

