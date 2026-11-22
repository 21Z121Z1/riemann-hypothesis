import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.DivMemLineLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0133
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0134
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicChartAtPoint

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBundleUnderEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem flagStep_linearEquiv_image {Ω F F' : Type} [Field Ω] [AddCommGroup F] [Module Ω F] [AddCommGroup F']
    [Module Ω F'] (Φ : F ≃ₗ[Ω] F') {r : ℕ} (d : Fin r → F) (i : ℕ) :
    flagStep Ω (fun k => Φ (d k)) i = (flagStep Ω d i).map Φ.toLinearMap := by
  unfold flagStep
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem isFlagVBOn_pull_map : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (E F F' : Type)
    [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (L : Lat ξ E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (T : Set (Cpt ξ')) (r : ℕ) (b : Fin r → F),
    (L.pull ξ' f j).IsFlagVBOn T b →
    (L.pull ξ' f (Φ.toLinearMap.toAddMonoidHom.comp j)).IsFlagVBOn T (fun k => Φ (b k)) := by
  intro X X' Ω₀ Ω _ _ ξ ξ' f E F F' _ _ _ _ _ _ L j Φ T r b h
  unfold Lat.IsFlagVBOn at h ⊢
  intro p hp
  obtain ⟨U, hpU, c, hc, hframe⟩ := h p hp
  refine ⟨U, hpU, fun k => Φ (c k), fun i => ?_, fun q hq hqU => ?_⟩
  · rw [flagStep_linearEquiv_image, flagStep_linearEquiv_image, hc i]
  · have hq' := hframe q hq hqU
    unfold Lat.IsFrameAt at hq' ⊢
    obtain ⟨hli, hsp⟩ := hq'
    refine ⟨hli.map' Φ.toLinearMap Φ.ker, ?_⟩
    let φ : F →ₗ[regAt ξ' q] F' := Φ.toLinearMap.restrictScalars (regAt ξ' q)
    unfold Lat.pull at hsp ⊢
    rw [show Set.range (fun k => Φ (c k)) = φ '' Set.range c from Set.range_comp φ c]
    rw [← Submodule.map_span φ, ← hsp, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨h, e, he, rfl⟩
      exact ⟨j e, ⟨h, e, he, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, e, he, rfl⟩, rfl⟩
      exact ⟨h, e, he, rfl⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCmTypeLatticeComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptWedge

section LinAlg

variable {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]

theorem exists_wedge_eq_smul {n : ℕ} {e b : Fin n → V} (h : ∀ k, e k ∈ Submodule.span Ω (Set.range b)) :
    ∃ d : Ω, exteriorPower.ιMulti Ω n e = d • exteriorPower.ιMulti Ω n b := by
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  have he : e = fun k => ∑ l, (Matrix.of T) k l • b l := funext fun k => (hT k).symm
  exact ⟨(Matrix.of T).det, by rw [he]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n b _⟩

theorem isPullWedge_smul_ιMulti (i : Ω₀ →+* Ω) (j : V₀ →+ V) (hj : IsExtOver i j) {n : ℕ} {u : Fin n → V₀}
    (hu : LinearIndependent Ω₀ u) {γ : Ω₀} (hγ : γ ≠ 0) :
    CptIn.IsPullWedge i j (γ • exteriorPower.ιMulti Ω₀ n u)
      (i γ • exteriorPower.ιMulti Ω n fun k => j (u k)) := by
  intro b α hab
  have hw := WedgeFrame.ιMulti_ne_zero hu
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hab
    exact smul_ne_zero hγ hw hab
  have hbe : exteriorPower.ιMulti Ω₀ n b = (α⁻¹ * γ) • exteriorPower.ιMulti Ω₀ n u := by
    rw [mul_smul, hab, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hm := GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional Ω₀ V₀ n b u _ hu (mul_ne_zero (inv_ne_zero hα) hγ) hbe
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω₀).1 (hm k)
  have hb : b = fun k => ∑ l, (Matrix.of T) k l • u l := funext fun k => (hT k).symm
  have h1 : exteriorPower.ιMulti Ω₀ n b = (Matrix.of T).det • exteriorPower.ιMulti Ω₀ n u := by
    rw [hb]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω₀ V₀ n u _
  have h2 : γ = α * (Matrix.of T).det := by
    rw [h1, smul_smul] at hab
    exact smul_left_injective Ω₀ hw hab
  have h3 : (fun k => j (b k)) = fun k => ∑ l, (i.mapMatrix (Matrix.of T)) k l • j (u l) := by
    funext k
    rw [hb]
    simp only [map_sum, hj.1]
    rfl
  rw [h3, GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n _ _, ← RingHom.map_det, smul_smul, ← map_mul, ← h2]

end LinAlg

theorem exists_eq_smul_ιMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {r : ℕ} {u : Fin r → E} {x : Cpt ξ} (hu : L.IsFrameAt u x)
    {a : ⋀[Ω]^r E} {α : Ω} (hα : α ≠ 0) (hw : L.wedge r x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ γ : Ω, γ ≠ 0 ∧ a = γ • exteriorPower.ιMulti Ω r u := by
  obtain ⟨h1, h2⟩ := WedgeFrame.wedge_eq_span_ιMulti X Ω ξ E L r u x hu
  have h3 : exteriorPower.ιMulti Ω r u ∈ Submodule.span (regAt ξ x) {α • a} := by
    rw [← hw, h1]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h3
  have ht' : ((t : Ω) * α) • a = exteriorPower.ιMulti Ω r u := by
    rw [mul_smul]; exact ht
  have ht0 : (t : Ω) * α ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht'
    exact h2 ht'.symm
  exact ⟨((t : Ω) * α)⁻¹, inv_ne_zero ht0, by rw [← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]⟩

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem tie_act {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (a : 𝓞 E) (e : Z.V) : j (Z.ρ a e) = 𝔐.ρ a (j e) := by
  obtain ⟨-, -, -, h4⟩ := h
  refine 𝔐.M.inj (Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [h4, Z.act a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc]
  exact (congrArg (· ≫ Over.Hom.left (Y.t.act.act a)) (h4 e).symm).trans (Category.assoc _ _ _)

theorem tie_mem_eigSp {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (σ : 𝓞 E →+* c.F) {e : Z.V} (he : e ∈ eigSp Z.ρ (Z.inc.comp σ)) :
    j e ∈ eigSp 𝔐.ρ (𝔐.cst.comp σ) := by
  have hi := h.2.1
  have hs := h.2.2.1.1
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← tie_act h, he a, hs, ← hi]
  rfl

theorem exists_side {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) {L : Lat (Z.ξ₀ ≫ Y.j) Z.V} {r : ℕ} {u : Fin r → Z.V} {x : Cpt (Z.ξ₀ ≫ Y.j)}
    (hu : L.IsFrameAt u x) {a : ⋀[Z.Ω]^r Z.V} {α : Z.Ω} (hα : α ≠ 0)
    (hw : L.wedge r x = Submodule.span (regAt (Z.ξ₀ ≫ Y.j) x) {α • a}) {B : Fin r → 𝔐.Li}
    (hB : ∀ k, j (u k) ∈ Submodule.span Ω (Set.range B)) :
    ∃ (a' : ⋀[Ω]^r 𝔐.Li) (d : Ω), d ≠ 0 ∧ a' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧
      a' = d • exteriorPower.ιMulti Ω r B := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_smul_ιMulti hu hα hw
  have hj : IsExtOver i j := h.2.2.1
  have hind : LinearIndependent Ω fun k => j (u k) := hj.2 r u hu.1
  have hne := WedgeFrame.ιMulti_ne_zero hind
  obtain ⟨d, hd⟩ := exists_wedge_eq_smul hB
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hd
    exact hne hd
  have hiγ : i γ ≠ 0 := (map_ne_zero i).2 hγ
  exact ⟨_, i γ * d, mul_ne_zero hiγ hd0, smul_ne_zero hiγ hne, isPullWedge_smul_ιMulti i j hj hu.1 hγ,
    by rw [hd, smul_smul]⟩

end Comparison₂

theorem exists_pullWedge_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), CptIn.IsTie Z 𝔐 i j → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → ∃ (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω), d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ a' ≠ 0 ∧ b' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧ CptIn.IsPullWedge i j b b' ∧ a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) ∧ b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 Fl τ i j a b hT hL
  have hfr : ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧
      x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 c.F)) x
    exact ⟨a, b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2, hab⟩
  obtain ⟨h1, h2, -, x, hx⟩ := isVBOn_eig_genFib E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y U Z τ.1
    ⟨FaithfulSMul.algebraMap_injective _ _, inferInstance, hfr⟩ τ.2
  obtain ⟨-, -, hg⟩ := hL
  obtain ⟨α, β, hα, hβ, hwa, hwb, -⟩ := hg x hx
  obtain ⟨W₁, hW₁, u₁, hs₁, hf₁⟩ := h1 x hx
  obtain ⟨W₂, hW₂, u₂, hs₂, hf₂⟩ := h2 x hx
  have hu₁ := hf₁ x hx hW₁
  have hu₂ := hf₂ x hx hW₂
  have hB₁ : ∀ k, j (u₁ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inl τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₁ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ.1)) := hs₁ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inl] at this
  have hB₂ : ∀ k, j (u₂ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inr τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₂ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ.1))) :=
      hs₂ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inr] at this
  obtain ⟨a', d₁, hd₁, ha', hpa, hea⟩ := exists_side hT hu₁ hα hwa (B := Fl.b (.inl τ)) hB₁
  obtain ⟨b', d₂, hd₂, hb', hpb, heb⟩ := exists_side hT hu₂ hβ hwb (B := Fl.b (.inr τ)) hB₂
  exact ⟨a', b', d₁, d₂, hd₁, hd₂, ha', hb', hpa, hpb, hea, heb⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptWedge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionWeilPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_torsion_weil_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ n : ℕ, FullTorsion G ξ n → FullTorsion G' ξ' n ∧ ∀ e, GenWeil G L ξ n e → ∃ e', GenWeil G' L' ξ' n e' ∧ ∀ (x g : Over.mk ξ ⟶ G) (x' g' : Over.mk ξ' ⟶ G'), x ^ n = 1 → g ^ n = 1 → x'.left ≫ φ = spMap i ≫ x.left → g'.left ≫ φ = spMap i ≫ g.left → (e' x' g' : Ω') = i (e x g) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.full_torsion_weil_pullback | exact GlobalTheory.CompanionTheory.Relay.full_torsion_weil_pullback | (intros; apply GlobalTheory.CompanionTheory.Relay.full_torsion_weil_pullback <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagUnderEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.Transport

theorem flagStep_equiv {Ω F F' : Type} [Field Ω] [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
    (Φ : F ≃ₗ[Ω] F') {r : ℕ} (b : Fin r → F) (i : ℕ) :
    flagStep Ω (fun k => Φ (b k)) i = (flagStep Ω b i).map Φ.toLinearMap := by
  rw [flagStep, flagStep, Submodule.map_span, Set.image_image]
  rfl

theorem isGenericFlag_transport : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E₀ E F F' : Type)
    [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E] [Module Ω₀ E] [AddCommGroup F] [Module Ω F]
    [AddCommGroup F'] [Module Ω F'] (a : E₀ ≃ₗ[Ω₀] E) (j : E →+ F) (Φ : F ≃ₗ[Ω] F') (S : Type) (r : S → ℕ)
    (V : S → Submodule Ω₀ E) (V₀ : S → Submodule Ω₀ E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ),
    (∀ s e, e ∈ V₀ s ↔ a e ∈ V s) → IsGenericFlag (Ω' := Ω) j V b d →
    IsGenericFlag (Ω' := Ω) ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) V₀
      (fun s k => Φ (b s k)) d := by
  intro Ω₀ Ω _ _ _ E₀ E F F' _ _ _ _ _ _ _ _ a j Φ S r V V₀ b d hV hG
  obtain ⟨c, u, hc, hjlin, hjc, hb, hu1, hu0, hflag, halg, hd, hrank⟩ := hG
  refine ⟨fun σ k => a.symm (c σ k), u, fun σ => ⟨?_, ?_⟩, ?_, fun σ => ?_, fun σ => ?_, hu1, hu0,
    fun σ i => ?_, halg, hd, hrank⟩
  · exact (hc σ).1.map' a.symm.toLinearMap a.symm.ker
  · have h1 : Submodule.span Ω₀ (Set.range fun k => a.symm (c σ k)) =
        (Submodule.span Ω₀ (Set.range (c σ))).map a.symm.toLinearMap := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1, (hc σ).2]
    ext e
    rw [hV σ e, Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  · intro x e
    show Φ (j (a (x • e))) = algebraMap Ω₀ Ω x • Φ (j (a e))
    rw [map_smul, hjlin, map_smul]
  · have hfe : (fun k => ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom)
        (a.symm (c σ k))) = ⇑Φ.toLinearMap ∘ fun k => j (c σ k) := by
      funext k
      show Φ (j (a (a.symm (c σ k)))) = Φ (j (c σ k))
      rw [LinearEquiv.apply_symm_apply]
    have h3 : LinearIndependent Ω (fun k => ((Φ.toLinearMap.toAddMonoidHom.comp j).comp
        a.toLinearMap.toAddMonoidHom) (a.symm (c σ k))) := by
      rw [hfe]
      exact (hjc σ).map' Φ.toLinearMap Φ.ker
    exact h3
  · exact (hb σ).map' Φ.toLinearMap Φ.ker
  · have hfun : (fun k => ∑ l, u σ l k •
        ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) (a.symm (c σ l))) =
        fun k => Φ (∑ l, u σ l k • j (c σ l)) := by
      funext k
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      show u σ l k • Φ (j (a (a.symm (c σ l)))) = u σ l k • Φ (j (c σ l))
      rw [LinearEquiv.apply_symm_apply]
    calc flagStep Ω (fun k => Φ (b σ k)) i = (flagStep Ω (b σ) i).map Φ.toLinearMap := flagStep_equiv Φ (b σ) i
      _ = (flagStep Ω (fun k => ∑ l, u σ l k • j (c σ l)) i).map Φ.toLinearMap := by rw [hflag σ i]
      _ = flagStep Ω (fun k => Φ (∑ l, u σ l k • j (c σ l))) i := (flagStep_equiv Φ _ i).symm
      _ = flagStep Ω (fun k => ∑ l, u σ l k •
          ((Φ.toLinearMap.toAddMonoidHom.comp j).comp a.toLinearMap.toAddMonoidHom) (a.symm (c σ l))) i := by
        rw [hfun]

end GlobalTheory.CompanionTheory.Ar.FlagStep.Transport
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramAt_conj_point_map_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L (spMap (starRingEnd ℂ) ≫ z) b (Γ.map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_period_linear_algebra : ∀ (p q g : ℕ) (T T' : (Fin g → ℂ) → (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ) (π : Fin p ⊕ Fin q → Fin g → ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ), IsLinearMap ℂ T → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → S.det ≠ 0 → LinearIndependent ℂ V → LinearIndependent ℂ W → (∀ n, T (π n) ∈ Submodule.span ℂ (Set.range V)) → (∀ n, T' (π n) ∈ Submodule.span ℂ (Set.range W)) → (∀ m n, hermForm Hm (T (π m)) (T (π n)) - star (hermForm Hm (T' (π m)) (T' (π n))) = 2 * Complex.I * S m n) → ∃! x : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × ℂ, (∀ n, T' (π n) = ∑ j, x.2.1 j n • W j) ∧ (∀ j n, ∑ m, x.1 j m * S m n = x.2.1 j n) ∧ x.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • π m) = V a) ∧ ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • π m) = V a) → (Matrix.fromRows C x.1).det = x.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra | exact GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra | (intros; apply GlobalTheory.CompanionTheory.Ar.LinFlat.flatSection_linearAlgebra <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagRead

open GlobalTheory.CompanionTheory.Ar.FlagPull

theorem fieldRange_finite {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω)
    (hfin : letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) :
    FiniteDimensional i.fieldRange Ω ∧
      Module.finrank i.fieldRange Ω = (letI := i.toAlgebra; Module.finrank Ω₁ Ω) := by
  letI := i.toAlgebra
  haveI := hfin
  let e : Ω₁ ≃+* i.fieldRange := RingEquiv.ofBijective i.rangeRestrictField
    ⟨fun x y h => i.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨a, Subtype.ext ha⟩⟩
  have he : (algebraMap i.fieldRange Ω).comp (e : Ω₁ →+* i.fieldRange) =
      ((RingEquiv.refl Ω : Ω ≃+* Ω) : Ω →+* Ω).comp (algebraMap Ω₁ Ω) := by
    ext x
    rfl
  exact ⟨Module.Finite.of_equiv_equiv e (RingEquiv.refl Ω) he,
    (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl Ω) he).symm⟩

theorem span_eq_of_indep {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b b' : Fin r → V}
    {W : Submodule Ω V} (hb : LinearIndependent Ω b) (hle : ∀ k, b k ∈ W) (hb' : LinearIndependent Ω b')
    (hs : Submodule.span Ω (Set.range b') = W) : Submodule.span Ω (Set.range b) = W := by
  subst hs
  haveI : FiniteDimensional Ω (Submodule.span Ω (Set.range b')) :=
    FiniteDimensional.span_of_finite Ω (Set.finite_range _)
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨k, rfl⟩
    exact hle k
  · rw [finrank_span_eq_card hb, finrank_span_eq_card hb']

theorem generic_read : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hfin hd hf hcst hj hpt hρ
  obtain ⟨hfd, hfr⟩ := fieldRange_finite i hfin
  haveI := hfd
  have hgen : genPt A.ξ₀ = genPt B.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt B.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_iso A.gen₀ B.gen₀ hgen
  have hfn : B.fn.comp ψ.toRingHom = i.comp A.fn := by
    haveI := mono_of_isCptGen A.gen₀
    have e1 : spMap B.fn ≫ B.ξ₀ = B.ξ ≫ B.f := B.fn_over.symm
    have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
    have e3 : B.ξ ≫ h = spMap i ≫ A.ξ := hd
    have e4 : spMap (B.fn.comp ψ.toRingHom) = spMap (i.comp A.fn) := by
      refine (cancel_mono A.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, FlagPull.spMap_comp, Category.assoc, Category.assoc, hψ, e1, e2, hf, ← Category.assoc, e3,
        Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  letI mod' : Module B.Ω₀ Fl.Li₀ := Module.compHom _ ψ.symm.toRingHom
  have hs : ∀ (a : A.Ω₀) (e : Fl.Li₀), ψ a • e = a • e := fun a e => by
    show ψ.symm (ψ a) • e = a • e
    rw [ψ.symm_apply_apply]
  have hemb : ∀ s, B.emb s = i.comp (A.emb s) := fun s => by
    simp only [HodgeCpt.emb]
    rw [hcst]
    rfl
  have hVgen : ∀ s w, jA w ∈ B.Vgen s ↔ w ∈ A.Vgen s := fun s w => by
    show jA w ∈ eigSp B.ρ (B.emb s) ↔ w ∈ eigSp A.ρ (A.emb s)
    rw [hemb]
    exact mem_eigSp_iff hj _ _ _ hρ w
  let V₀' : CMType H ⊕ CMType H → Submodule B.Ω₀ Fl.Li₀ := fun s =>
    { carrier := (Fl.V₀ s : Set Fl.Li₀)
      add_mem' := fun ha hb => (Fl.V₀ s).add_mem ha hb
      zero_mem' := (Fl.V₀ s).zero_mem
      smul_mem' := fun c x hx => (Fl.V₀ s).smul_mem (ψ.symm c) hx }
  have hsq : spMap (dualMap i) ≫ spMap (dualMap A.fn) = spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    rw [← FlagPull.spMap_comp, ← FlagPull.spMap_comp, ← dualMap_comp, ← dualMap_comp, hfn]
  have hspan : ∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s := by
    intro s
    letI := A.fn.toAlgebra
    obtain ⟨cc, u, hcV, -, -, hb, -, -, hfl, -⟩ := Fl.generic
    have hmemc : ∀ k, Fl.j (cc s k) ∈ A.Vgen s := fun k => (Fl.V₀_mem s _).1 (by
      rw [← (hcV s).2]
      exact Submodule.subset_span ⟨k, rfl⟩)
    have hbk : ∀ a, Fl.b s a ∈ A.Vgen s := by
      intro a
      have h1 : Fl.b s a ∈ flagStep Ω₁ (Fl.b s) (labelRk D s) := Submodule.subset_span ⟨a, a.2, rfl⟩
      rw [hfl s] at h1
      refine (Submodule.span_le (p := A.Vgen s).2 ?_) h1
      rintro _ ⟨k, -, rfl⟩
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmemc l)
    obtain ⟨U, hU, b', hb', hfr'⟩ := B.vb s ⟨genPt B.ξ, specializes_rfl⟩ (Set.mem_univ _)
    exact span_eq_of_indep (hj.2 _ _ (hb s)) (fun k => (hVgen s _).2 (hbk k))
      (hfr' _ (Set.mem_univ _) hU).1 hb'
  refine ⟨Fl.Li₀, Fl.acg, mod', transport ψ hψ hs Fl.M₀, jA.comp Fl.j, V₀', hspan, fun e => ?_,
    fun s e => (Fl.V₀_mem s e).trans (hVgen s _).symm, ?_⟩
  · show (B.M.pt (jA (Fl.j e))).left ≫ B.m.φ =
      spMap (dualMap B.fn) ≫ spMap (dualMap ψ.toRingHom) ≫ (Fl.M₀.pt e).left
    rw [hpt, Fl.j_pt, ← Category.assoc, hsq, Category.assoc]
  · have := genericFlag_pull A.fn B.fn ψ i hfn hs Fl.j jA hj Fl.V₀ V₀' (fun _ _ => Iff.rfl) Fl.b Fl.deg Fl.generic
    rw [hfr] at this
    exact this

end GlobalTheory.CompanionTheory.Ar.FlagRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistAutomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_twist_automorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∃ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA : SABMap tΩ A.t A.ξ) (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      mA.φ = m.φ ≫ k.φ ∧ mA.φ ≫ A.m.φ = u.φ ≫ Y.m.φ ∧ mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ ∧
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ ∧
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) ∧ (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) ∧ (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) ∧ (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre | exact GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGeneratedSumSpecializationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_generated_sum_specialization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∀ k, ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.M.lat ⟨centre z, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat.frame_mem_lat | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat.frame_mem_lat | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameLat.frame_mem_lat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_pullback_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (k : ℕ) (v' : Fin k → (epsAt x' ⟶ t'.G)) (v : Fin k → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x = x' ≫ f → (∀ a, (v' a).left ≫ m.φ = (v a).left) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_of_sabMap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAffinePolydiscChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hol_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ) (T : Set X), SmoothOfRelativeDimension d s → Geo.ResK.HasSncCoords s d T → ∀ (x : Sp ℂ ⟶ X) (W : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ∃ (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W ∧ a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ Set.InjOn ψ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ (centre (spMap (ψ z) ≫ hV.fromSpec) ∉ T ↔ z ∈ punct d a 1)) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = spMap (ψ (κ b)) ≫ hV.fromSpec :=
  @PositivityTheory.Xgn.exists_holomorphic_chart_at_point

end GlobalTheory.CompanionTheory.Ar.Flat
end

