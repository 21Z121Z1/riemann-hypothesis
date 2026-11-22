import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0642
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkCharZeroEssFiniteType
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GModStalk

theorem charZero_essFiniteType_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X),
    CharZero (Z.X.presheaf.stalk z) ∧ Algebra.EssFiniteType ℤ (Z.X.presheaf.stalk z) := by
  intro E _ _ _ H D l Xo c Z z
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨-, hft, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  haveI : Flat Z.s := Z.flat
  let y : PrimeSpectrum (𝓞 c.F) := Z.s z
  letI : Algebra (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z))
  have h₁ : (Z.s.stalkMap z).hom.EssFiniteType := LocallyOfFiniteType.stalkMap Z.s z
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have hσ : Function.Injective (Z.s.stalkMap z).hom := by
    have h := Flat.stalkMap Z.s z
    algebraize [(Z.s.stalkMap z).hom]
    have : IsLocalHom (algebraMap ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)) :=
      Z.s.toLRSHom.prop z
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp (𝓞 c.F)).presheaf.stalk (Z.s z))
      (B := Z.X.presheaf.stalk z)
    exact FaithfulSMul.algebraMap_injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)
  refine ⟨charZero_of_injective_ringHom (f := (Z.s.stalkMap z).hom.comp φ) (hσ.comp hφ), ?_⟩
  have hO : Algebra.EssFiniteType ℤ (𝓞 c.F) := inferInstance
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hO).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

end GlobalTheory.GModStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv TanM)
open scoped MonObj
open GlobalTheory.LieMet (tanOf isTan_tv tan_ext pushE left_pushE isTan_map)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.StepBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Dual

variable {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V)
  {n : ℕ} {m : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)} {b : Fin n → (Sp (DualNumber S) ⟶ t.G.left)}
  (hb : ∀ j, IsTanAtG t x (b j)) {A B : Matrix (Fin n) (Fin n) S} (hB : ∀ l j, tanEv t (hb j) h (m l) = B l j)

include hB in

theorem tanEv_eq_mulVec {cf : Fin n → S} {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x w)
    (hc : IsCombAtG t x b cf w) : (fun l => tanEv t hw h (m l)) = B.mulVec cf := by
  funext l
  rw [GlobalTheory.LocM.tanEv_comb E H X t S x V h n b hb cf w hw hc]
  exact Finset.sum_congr rfl fun j _ => by rw [hB, _root_.mul_comm]

include hB in

theorem coeff_eq (hAB : A * B = 1) {cf : Fin n → S} {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x w)
    (hc : IsCombAtG t x b cf w) : cf = A.mulVec fun l => tanEv t hw h (m l) := by
  rw [tanEv_eq_mulVec h hb hB hw hc, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

include hB in

theorem isComb_dual (hm : VB.IsFrame m) (hBA : B * A = 1) {w : Sp (DualNumber S) ⟶ t.G.left} (hw : IsTanAtG t x w) :
    IsCombAtG t x b (A.mulVec fun l => tanEv t hw h (m l)) w := by
  have hc := (LieMet.isComb_iff (fun j => tanOf (hb j)) (A.mulVec fun l => tanEv t hw h (m l)) _).2 rfl
  have e := tanEv_eq_mulVec h hb hB (isTan_tv _) hc
  rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at e
  have e' := (GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x V h n m hm fun l => tanEv t hw h (m l)).unique
    ⟨isTan_tv _, congrFun e⟩ ⟨hw, fun _ => rfl⟩
  rw [e'] at hc
  exact hc

end Dual

section Transport

variable {X X₁ X₂ : Scheme.{0}} {t : SAB H X} {t₁ : SAB H X₁} {t₂ : SAB H X₂} {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
  (m₁ : SABMap t₁ t f₁) (m₂ : SABMap t₂ t f₂) {S : Type} [CommRing S] {x₁ : Sp S ⟶ X₁} {x₂ : Sp S ⟶ X₂}
  (hx : x₁ ≫ f₁ = x₂ ≫ f₂)

include hx in

theorem exists_corr {w : Sp (DualNumber S) ⟶ t₂.G.left} (hw : IsTanAtG t₂ x₂ w) :
    ∃ v, IsTanAtG t₁ x₁ v ∧ v ≫ m₁.φ = w ≫ m₂.φ :=
  ⟨_, isTan_tv ((pushE m₁ x₁ hx).symm (pushE m₂ x₂ rfl (tanOf hw))), by
    rw [← left_pushE m₁ x₁ hx, LinearEquiv.apply_symm_apply]
    rfl⟩

include hx in

theorem isComb_corr {n : ℕ} {b₁ : Fin n → (Sp (DualNumber S) ⟶ t₁.G.left)} {b₂ : Fin n → (Sp (DualNumber S) ⟶ t₂.G.left)}
    (h₁ : ∀ j, IsTanAtG t₁ x₁ (b₁ j)) (h₂ : ∀ j, IsTanAtG t₂ x₂ (b₂ j)) (hb : ∀ j, b₁ j ≫ m₁.φ = b₂ j ≫ m₂.φ)
    {w₁ : Sp (DualNumber S) ⟶ t₁.G.left} {w₂ : Sp (DualNumber S) ⟶ t₂.G.left} (k₁ : IsTanAtG t₁ x₁ w₁)
    (k₂ : IsTanAtG t₂ x₂ w₂) (hw : w₁ ≫ m₁.φ = w₂ ≫ m₂.φ) {cf : Fin n → S} (hc : IsCombAtG t₁ x₁ b₁ cf w₁) :
    IsCombAtG t₂ x₂ b₂ cf w₂ := by
  have e := (LieMet.isComb_iff (fun j => tanOf (h₁ j)) cf (tanOf k₁)).1 hc
  refine (LieMet.isComb_iff (fun j => tanOf (h₂ j)) cf (tanOf k₂)).2 ((pushE m₂ x₂ rfl).injective ?_)
  have e₁ : pushE m₂ x₂ rfl (tanOf k₂) = pushE m₁ x₁ hx (tanOf k₁) := tan_ext hw.symm
  have e₂ (j) : pushE m₂ x₂ rfl (tanOf (h₂ j)) = pushE m₁ x₁ hx (tanOf (h₁ j)) := tan_ext (hb j).symm
  rw [e₁, e, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul, e₂]

include hx in

theorem exists_dual_basis {V : X₁.Opens} (h : ⊤ ≤ x₁ ⁻¹ᵁ V) {n : ℕ} {m : Fin n → Γ(GlobalTheory.LieVB.omega t₁.G, V)}
    (hm : VB.IsFrame m) (a : GL (Fin n) S) :
    ∃ v : Fin n → (Sp (DualNumber S) ⟶ t₂.G.left), (∀ j, IsTanAtG t₂ x₂ (v j)) ∧
      (∀ u, IsTanAtG t₂ x₂ u → ∃! cf, IsCombAtG t₂ x₂ v cf u) ∧
      ∀ (k : Type) [CommRing k] (φ : S →+* k) (y₁ : Sp k ⟶ X₁) (y₂ : Sp k ⟶ X₂), spMap φ ≫ x₁ = y₁ → spMap φ ≫ x₂ = y₂ →
        ∀ u, IsTanAtG t₂ y₂ u → ∃ (w : Sp (DualNumber k) ⟶ t₁.G.left) (hw : IsTanAtG t₁ y₁ w) (h' : ⊤ ≤ y₁ ⁻¹ᵁ V),
          w ≫ m₁.φ = u ≫ m₂.φ ∧ IsCombAtG t₂ y₂ (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ v j)
            (fun j => ∑ l, φ (a j l) * tanEv t₁ hw h' (m l)) u := by
  choose b hb hbe using fun j : Fin n =>
    (GlobalTheory.TanFibre.existsUnique_tanEv E H X₁ t₁ S x₁ V h n m hm fun l => (a⁻¹).1 l j).exists
  choose v hv hve using fun j => exists_corr m₂ m₁ hx.symm (hb j)
  refine ⟨v, hv, fun u hu => ?_, ?_⟩
  · obtain ⟨w, hw, e⟩ := exists_corr m₁ m₂ hx hu
    exact ⟨_, isComb_corr m₁ m₂ hx hb hv (fun j => (hve j).symm) hw hu e
      (isComb_dual h hb (A := a.1) (fun l j => hbe j l) hm a.inv_mul hw), fun cf hc =>
      coeff_eq h hb (fun l j => hbe j l) a.mul_inv hw (isComb_corr m₂ m₁ hx.symm hv hb hve hu hw e.symm hc)⟩
  · rintro k _ φ _ _ rfl rfl u hu
    have hx' : (spMap φ ≫ x₁) ≫ f₁ = (spMap φ ≫ x₂) ≫ f₂ := by rw [Category.assoc, Category.assoc, hx]
    have h' : ⊤ ≤ (spMap φ ≫ x₁) ⁻¹ᵁ V := (spMap φ).preimage_mono h
    obtain ⟨w, hw, e⟩ := exists_corr m₁ m₂ hx' hu
    have hb' (j) := isTan_map φ rfl (hb j)
    have hv' (j) := isTan_map φ rfl (hv j)
    have hc := isComb_dual h' hb' (A := a.1.map φ) (B := (a⁻¹).1.map φ) (fun l j => by
      rw [GlobalTheory.LocM.tanEv_baseChange E H X₁ t₁ S x₁ V h (b j) (hb j) k φ, hbe]
      rfl) hm (by rw [← Matrix.map_mul, a.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one]) hw
    exact ⟨w, hw, h', e, isComb_corr m₁ m₂ hx' hb' hv' (fun j => by rw [Category.assoc, Category.assoc, hve]) hw hu e hc⟩

end Transport

section Models

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

theorem isFrame_incl {Z : Mdl Y i₀} {V : Z.X.Opens} {n : ℕ} {m : Fin n → Γ((Lat.top Z).N.toMod, V)} (hm : VB.IsFrame m) :
    VB.IsFrame fun l => (Lat.top Z).N.incl.app V (m l) :=
  have : IsIso (Lat.top Z).N.incl := Twist.isIso_of_bijective _ fun V =>
    ⟨(Lat.top Z).N.incl_app_injective V, fun s => ⟨⟨s, (Lat.isTop_top V).ge trivial⟩, rfl⟩⟩
  hm.map_iso (Lat.top Z).N.incl

theorem exists_isTrans {Z Z' : Mdl Y i₀} {g : Z'.X ⟶ Z.X} (hg : IsMap Z' Z g) (x : Z'.X) :
    ∃ (τ : (Y Z'.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z'.i).t (Y Z.i).t τ), LocM.IsTrans Z.i Z'.i τ mu ∧
      g ≫ Z.π = Z'.π ≫ τ := by
  have : Nonempty Z'.X := ⟨x⟩
  obtain ⟨z, hz⟩ := Z'.dense.nonempty
  obtain ⟨τ, mu, -, htr, -⟩ := hg.2 (Z'.X.residueField z) (Z'.X.fromSpecResidueField z) (by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply z a).symm ▸ hz)
  exact ⟨τ, mu, htr, CommonMod.comp_π_eq hg htr⟩

end Models

theorem exists_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z Z' : Mdl Y i₀) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ), Step.Holds ⟨Z, Lat.top Z, σ, r, hr⟩ Z' → ∀ x : Z'.X, ∃ (U : Z'.X.Opens) (hU : IsAffineOpen U) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Z'.X, U)) ⟶ (Y Z'.i).t.G.left)), x ∈ U ∧ (∀ j, IsTanAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) (v j)) ∧ (∀ u, IsTanAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) u → ∃! cf, IsCombAtG (Y Z'.i).t (hU.fromSpec ≫ Z'.π) v cf u) ∧ ∀ (k : Type) [Field k] (φ : Γ(Z'.X, U) →+* k) (u : Vecs Dw (Y Z'.i).t k), Z'.FlagAt (spMap φ ≫ hU.fromSpec) u → ∀ i : Fin (Dw.mult σ), (i : ℕ) < r → ∃ cf : Fin n → k, (∀ j : Fin n, r ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG (Y Z'.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z'.π) (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ v j) cf (u σ i) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z Z' σ r hr hH x
  obtain ⟨-, g, hg, hS⟩ := hH
  dsimp only at g hg hS
  obtain ⟨U, hU, V, n, m, a, hxU, hUV, hm, hcl⟩ := hS x
  refine (exists_isTrans hg x).elim fun τ h₀ => h₀.elim fun mu h₁ => ?_
  have htr := h₁.1
  have hπ := h₁.2
  have h : ⊤ ≤ (hU.fromSpec ≫ g) ⁻¹ᵁ V := hU.fromSpec_preimage_self.ge.trans (hU.fromSpec.preimage_mono hUV)
  have hx : (hU.fromSpec ≫ g) ≫ Z.π = (hU.fromSpec ≫ Z'.π) ≫ τ :=
    (Category.assoc _ _ _).trans ((congrArg (hU.fromSpec ≫ ·) hπ).trans (Category.assoc _ _ _).symm)
  have hm' := isFrame_incl hm
  have hd := exists_dual_basis Z.tMap mu hx h hm' a
  refine hd.elim fun v hv => ⟨U, hU, n, v, hxU, hv.1, hv.2.1, fun k _ φ u hu i hi => ?_⟩
  have hu' : IsTanAtG (Y Z'.i).t ((spMap φ ≫ hU.fromSpec) ≫ Z'.π) (u σ i) := by
    exact hu.elim fun _ h₂ => h₂.elim fun _ hf => (hf.2.1.1 σ i).1
  have hw := hv.2.2 k φ ((spMap φ ≫ hU.fromSpec) ≫ g) _ (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm _ hu'
  exact hw.elim fun w h₂ => h₂.elim fun hw h₃ => h₃.elim fun h' e =>
    ⟨_, hcl k φ w hw h' ⟨τ, mu, u, i, htr, hu, hi, e.1⟩, e.2⟩

end GlobalTheory.LocM.StepBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsOfMap
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.MapComp
open GlobalTheory.LocM.CommonMod

namespace GlobalTheory.LocM.StepMono

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem inStep_comp {Z' Z B : Mdl Y i₀} {f : Z'.X ⟶ Z.X} {g : Z.X ⟶ B.X} (hf : IsMap Z' Z f) (hg : IsMap Z B g)
    {σ : E →+* ℂ} {r : ℕ} {k : Type} [Field k] {w : Sp k ⟶ Z'.X} {v : Sp (DualNumber k) ⟶ B.t.G.left}
    (h : InStep Z' B σ r w v) : InStep Z B σ r (w ≫ f) v := by
  obtain ⟨τ, mu, u, i, t, fu, hi, hv⟩ := h
  obtain ⟨τ₁, mu₁, u₁, t₁, e₁, fu₁, fu₁'⟩ := hf.2 k w (range_subset_opn Z' fu)
  have f₂ := flagAt_push hf.1.2.2 mu₁ e₁ fu₁ fu fu₁'
  obtain ⟨τ₂, mu₂, -, t₂, -⟩ := hg.2 k (w ≫ f) (range_subset_opn Z f₂)
  obtain ⟨mu', hmu'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₂ mu₁
  have t' := isTrans_comp hg.1.1 hf.1.1 t₂ t₁ mu' hmu'
  obtain ⟨-, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ _ _ mu mu' (hg.1.2.1.trans hf.1.2.1) t t'
  obtain ⟨a, φ, ha, gu, -⟩ := fu
  obtain ⟨y, hy, -⟩ := exists_lift_chart Z' ha
  refine ⟨τ₂, mu₂, _, i, t₂, f₂, hi, hv.trans ?_⟩
  rw [hmu k y _ _ _ (by rw [hy]; exact (gu.1 σ i).1.1), hmu', Category.assoc]

theorem tanEv_congr {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x x' : Sp k ⟶ X} (e : x = x')
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ (hv' : IsTanAtG t x' v) (h' : ⊤ ≤ x' ⁻¹ᵁ V), ∀ s, tanEv t hv h s = tanEv t hv' h' s := by
  subst e
  exact ⟨hv, h, fun _ => rfl⟩

theorem map_entry {R S T : Type} [CommRing R] [CommRing S] [CommRing T] {n : ℕ} (ψ : R →+* S) (φ : S →+* T)
    (a : GL (Fin n) R) (j l : Fin n) : φ (Matrix.GeneralLinearGroup.map ψ a j l) = φ.comp ψ (a j l) := rfl

theorem holds_of_isMap (t : Step Y i₀) {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) (h : t.Holds Z) :
    t.Holds Z' := by
  obtain ⟨hk, g, hg, H₀⟩ := h
  refine ⟨hf.1.2.2 _ hk, f ≫ g, isMap_comp hf hg, fun x => ?_⟩
  obtain ⟨U, hU, V, n, m, a, hx, hUV, hm, H₁⟩ := H₀ (f x)
  obtain ⟨_, ⟨U', hU', rfl⟩, hx', hle⟩ := Z'.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((f ⁻¹ᵁ U : Z'.X.Opens) : Set Z'.X) from hx) (f ⁻¹ᵁ U).2
  have e : U' ≤ f ⁻¹ᵁ U := hle
  refine ⟨U', hU', V, n, m, Matrix.GeneralLinearGroup.map (f.appLE U U' e).hom a, hx',
    e.trans (f.preimage_mono hUV), hm, fun k _ φ v hv hh hs j hj => ?_⟩
  have ep : (spMap φ ≫ hU'.fromSpec) ≫ f = spMap (φ.comp (f.appLE U U' e).hom) ≫ hU.fromSpec := by
    rw [← sp_comp, Category.assoc, Category.assoc]
    exact congrArg (spMap φ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec f hU hU' e).symm
  have eq : (spMap φ ≫ hU'.fromSpec) ≫ f ≫ g = (spMap (φ.comp (f.appLE U U' e).hom) ≫ hU.fromSpec) ≫ g := by
    rw [← ep]
    simp only [Category.assoc]
  have hs' := inStep_comp hf hg hs
  rw [ep] at hs'
  obtain ⟨hv', hh', he⟩ := tanEv_congr t.B.t eq hv hh
  exact (Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (map_entry _ φ a j l) (he _)).trans
    (H₁ k _ v hv' hh' hs' j hj)

theorem holds_mono : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (t : Step Y i₀) (Z Z' : Mdl Y i₀), (∃ f, IsMap Z' Z f) → t.Holds Z → t.Holds Z' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ t _ _ ⟨_, hf⟩ h => holds_of_isMap t hf h

end GlobalTheory.LocM.StepMono
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNormsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.successive_minima_positive_norms : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (g : ℕ) (J : Type) [Fintype J] (h : J → Fin g → C), (∀ c : Fin g → C, (∀ j, ∑ i, h j i * c i = 0) → c = 0) → ∀ (m : ℕ) (a : Fin m → Fin g → C), LinearIndependent C a → ∀ (N : Fin m → ℝ), (∀ l, N l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, h j i * ∑ l', cf l' * a l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}) → (∀ l, 0 < N l) ∧ ∀ (k : ℕ) (hk : k ≤ m), ∏ l : Fin k, N (Fin.castLE hk l) = ⨆ σ : Fin k → J, ‖∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s‖ := by
  first | exact @GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor | exact GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor | (intros; apply GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumMulEqOfSumToRealEq
section
noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section OfCover

variable {X : Type} [AddCommGroup X]

theorem sum_mul_eq_of_sum_toReal_eq {L ι κ : Type} [AddCommGroup L] [Fintype ι] [Fintype κ]
    {j : L →ₗ[ℤ] LinearMap.BilinForm ℤ X} (hj : Function.Injective j) (ℓ : L →ₗ[ℤ] ℤ) {u : ι → L} {w : κ → L}
    {a : ι → ℝ} {b : κ → ℝ} (h : ∑ i, a i • toReal (j (u i)) = ∑ k, b k • toReal (j (w k))) :
    ∑ i, a i * (ℓ (u i) : ℝ) = ∑ k, b k * (ℓ (w k) : ℝ) := by
  have := sum_mul_eq_zero_of_sum_toReal hj ℓ (β := Sum.elim u w) (c := Sum.elim a (-b)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, h, add_neg_cancel])
  rw [Fintype.sum_sum_type] at this
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
  linarith

theorem toReal_injective : Function.Injective (toReal : LinearMap.BilinForm ℤ X → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply] at this
    exact_mod_cast this

end OfCover

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumRankOneIntegralRescalingStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_rank_one_integral_rescaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (d : ℕ) (ξ : Fin d → Fin N → E) (t : Fin d → E), (∀ j, cc (t j) = t j) → ∃ (k : ℕ) (ξ' : Fin d → Fin N → E) (s : Fin d → E), 0 < k ∧ (∀ j, ξ' j ∈ X.Λ) ∧ (∀ j, ∃ a : E, ξ' j = a • ξ j) ∧ (∀ j, cc (s j) = s j) ∧ (∀ j, IsIntegral ℤ (s j)) ∧ (k : E) • (∑ j, (t j * X.κ0) • rk1 X.Gm (ξ j) (ξ j)) = ∑ j, (X.m * s j * X.κ0) • rk1 X.Gm (ξ' j) (ξ' j) := by
  first | exact @GlobalTheory.UnipKill.scaleDecomp | exact GlobalTheory.UnipKill.scaleDecomp | (intros; apply GlobalTheory.UnipKill.scaleDecomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConstaStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_uniformisedChartFibre_eq_familyConstant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∀ (w : ℂ), Ha.T < w.im → ∀ (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → ∀ K : ℂ, (∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (K * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z)) → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → c₀ = K := by
  first | exact @GlobalTheory.ArcThetaFib.const_eq | exact GlobalTheory.ArcThetaFib.const_eq | (intros; apply GlobalTheory.ArcThetaFib.const_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionUniformisationEqRestrictCharactersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsion_uniformisation_eq_restrictCharacters : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') [CharZero R] [CharZero W], AdmBase R (maximalIdeal R) → AdmBase W (maximalIdeal W) →
    ∀ (g : R →+* W) (m : SABMap t' t (spMap g))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    α.comp ψ = β.comp g → n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
      (O : ValuationSubring F) (φ : W →+* O), IsLocalHom φ →
      (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ := by
  first | exact @GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict | exact GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict | (intros; apply GlobalTheory.ToricTorsionCompare.toric_torsion_eq_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_representable_finite_free : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  first | exact @GlobalTheory.TorsionRep.exists_finite_free_torsion_rep | exact GlobalTheory.TorsionRep.exists_finite_free_torsion_rep | (intros; apply GlobalTheory.TorsionRep.exists_finite_free_torsion_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil <;> assumption)
end

