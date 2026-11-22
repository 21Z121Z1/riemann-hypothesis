import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAbelianSchemeProjectiveClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TripleStOfLaws
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EigensectionSupport
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.UT

theorem eigensection_support : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (q : QkPt D.toPre F N) τ, q.y = 0 → IsTor τ q.g → ∀ x, QkToAkU U.toUnifPre F N q x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (t t' : SecA A F N) (s : Fam D.toPre F N) (c : F), U.ExpandsF F N w₀ t s → IsActOf A.A A.L N θ t t' → (∀ j, t'.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j) → ∀ β, (τ (Multiplicative.ofAdd β)).val ≠ c → ∀ j, (s.s β).f j = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN q τ hy hτ x hx θ hθ w₀ hw₀ t t' s c hs hact ht β hβ j
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hI D F N hN q).1
  have h₁ := (expBijF_and_expandsF_lin hL R I hI D A G hG U).2 F N w₀ t t t' s s (c - 1) hs hs (fun i => by
    rw [ht i]
    simp only [liftFun, map_sub, map_one, sub_mul, _root_.one_mul, sub_add_cancel])
  have h₂ := symLift_acts_as_phi hL R I hI D A G hG U F N hN q x hx θ hθ w₀ hw₀ w hw t t' s _ hs h₁ hact
  have h₃ := ((TorusWeight.torus_weight hL R I hI D A G hG U F N hN q τ hy hτ w hw).2 _ _).1 h₂ β j
  rw [sub_smul, one_smul, sub_add_cancel, DVR.smul_f, constBF_eq] at h₃
  have key : ∀ {S : Type} [CommRing S] (g : F →+* S) (a b : F) (y : S), a ≠ b → g b * y = g a * y → y = 0 := by
    intro S _ g a b y hab e
    have hu : IsUnit (g (a - b)) := (IsUnit.mk0 _ (sub_ne_zero.2 hab)).map g
    exact hu.mul_right_eq_zero.1 (by rw [map_sub, sub_mul, e, sub_self])
  exact key ((((DegPre.BF D.toPre F).left.presheaf.map (homOfLE le_top).op).hom).comp (gF D.toPre F)) _ c _ hβ h₃

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosExtTMap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.ClosureExample

theorem exists_adm (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) :
    ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ := by
  obtain ⟨s, hs⟩ := S.fg
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  let t₀ : Option s → Ω := fun j => j.elim 1 Subtype.val
  have htop : Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) = ⊤ := by
    set F := Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) with hF
    have hR : ∀ a ∈ S.R, a ∈ F := by
      intro a ha
      rw [← hs] at ha
      induction ha using Algebra.adjoin_induction with
      | mem x hx =>
        refine Subfield.subset_closure (Or.inr ⟨(x₀, none), (x₀, some ⟨x, hx⟩), ?_⟩)
        simp only [t₀, Option.elim]
        field_simp
      | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy
    refine top_unique fun x _ => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := S.frac x
    exact div_mem (hR a ha) (hR b hb)
  obtain ⟨M, U₀, h, -⟩ := GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω S (Option s) t₀ ⟨none, one_ne_zero⟩ (by
    rw [htop]
    exact Module.Finite.of_surjective (Algebra.linearMap (⊤ : Subfield Ω) Ω) fun x => ⟨⟨x, trivial⟩, rfl⟩)
  exact ⟨M, U₀, h⟩

theorem exists_clos_ext_tMap : GlobalTheory.UT.LL → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (S : ThetaSys o Ω) (ρ : S.Real), S.g = 1 ∧ S.Big ∧ (S.HasTests → ρ.HasGeo → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE ∧ ∃ Q : Clos ρ M U₀ EE, Nonempty Q.Ext ∧ ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), Nonempty (Q.TMap t c)) := by
  intro hL
  obtain ⟨o, Ω, _, _, _, _, S, hg, hbig, ⟨ρ⟩⟩ := GlobalTheory.T.exists_theta_system_genus_one hL.1 hL.2.1
  refine ⟨o, Ω, _, _, _, ‹_›, S, ρ, hg, hbig, fun hT hG => ?_⟩
  obtain ⟨M, U₀, hA⟩ := exists_adm o Ω S
  obtain ⟨EE, hE, -⟩ := GlobalTheory.ZH.exists_isEE_of_adm o Ω S M U₀ hT hA
  have hB := GlobalTheory.ZH.baseFacts_of_isEE o Ω S M U₀ EE hT hA.1 hE
  obtain ⟨Q⟩ := GlobalTheory.ZH.nonempty_clos hL o Ω S ρ M U₀ EE hB
  obtain ⟨h1, h2⟩ := GlobalTheory.ZH.exists_geoTest_tMap_and_centre hL o Ω S ρ M U₀ EE hB Q hbig hG
  have := hB.jac
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (X := M.Z) (Z := Set.univ) ⟨genericPoint M.Z, trivial⟩
    isClosed_univ.isLocallyClosed
  obtain ⟨p, hp, y, hy⟩ := h2 z hz
  obtain ⟨y₀, t, c, hc⟩ := h1 p y hy.2
  exact ⟨M, U₀, EE, hB, Q, GlobalTheory.ZH.ClosureLifting.nonempty_ext hL o Ω S ρ M U₀ EE hB Q, p, hp, y, y₀, t, c, hc⟩

end GlobalTheory.ZH.ClosureExample
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFormCorrectionNextThickeningLocalStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_correction_next_thickening_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, (∀ z (k : (H (e + 1)).ι) (k' : (H e).ι), (β e) z ∈ (H (e + 1)).U k → z ∈ (H e).U k' → gs (β e) z _ ((s (e + 1) j).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e j).f k'))) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ t₀ : ℕ, ∀ t, t₀ ≤ t → ∀ (e : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k : (H e).ι, MvPolynomial.eval₂Hom (cst ((Y (e)).hom ≫ thick R I (e)) ((H e).U k)) (fun j => (s e j).f k) (F) = 0) → ∃ G : MvPolynomial (Fin (n + 1)) R, G.IsHomogeneous t ∧ (∀ d, MvPolynomial.coeff d G ∈ I ^ (e + 1)) ∧ (∀ k : (H (e + 1)).ι, MvPolynomial.eval₂Hom (cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) ((H (e + 1)).U k)) (fun j => (s (e + 1) j).f k) (F - G) = 0) := by
  first | exact @GlobalTheory.Degen.exists_form_correction_local | exact GlobalTheory.Degen.exists_form_correction_local | (intros; apply GlobalTheory.Degen.exists_form_correction_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianGroupSchemeCubicalBundleClosureStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_groupScheme_cubical_bundle_closure : Laws → Laws2 → ThmUSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ex.core.HasTests → ex.core.Indep → ex.core.HasCharts → ex.core.TorsSec (S.r * S.N) → (∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀))) → ∃ Z : ZHPre ρ M U₀, (∃ e : Z.G.left ≅ Q.G.toScheme, e.hom ≫ Q.G.ι ≫ Q.P.hom = Z.G.hom ∧ Z.u₀ = Q.u₀ ∧ HEq (Z.φ ≫ e.hom) ex.a) ∧ Z.LocTheta ∧ Nonempty ex.core.Law := by
  first | exact @GlobalTheory.ClosureGroup.exists_pre | exact GlobalTheory.ClosureGroup.exists_pre | (intros; apply GlobalTheory.ClosureGroup.exists_pre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPointComplexDegenerationSmall
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem isThetaPt_classical (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (P : PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ)
    {I : Type} (x : I → (baseOver (Sp ℂ) ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0) (hx : ∀ i, x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))) :
    IsThetaPt P N x fun i => fnOf (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
      θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ))) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨hN, isUnit_natCast_sp hN0, fun q => ⟨⊤, trivial, ?_⟩⟩
  let T : Over (Sp ℂ) := overRes (T := baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ overResι (T := baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have htor : ∀ i, x i ^ (N ^ 2) = 1 := fun i => by
    rw [hx]
    refine (ThetaClassical.ex_nsmul u _ _).symm.trans ((u.ker _).2 ?_)
    rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_pow, smul_inv_smul₀ (pow_ne_zero _ hN0)]
    exact (l i).2
  have key := ThetaClassical.isThetaPtOver hL hL2 hT P u Hm χ θ N T p (fun i => overResι ⊤ ≫ x i) l
    hN hAH hθ h0 (fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x i) hp).trans
      ((Category.id_comp _).trans (hx i))))
    (fun i => ThetaClassical.exists_symLift hL P (N ^ 2) _ (by push_cast; rfl) hN.pow (x i) (htor i))
  convert key using 2 with i
  exact ThetaClassical.constFn_top _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso (D : Datum H) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (Q : PolAV (Sp ℂ)) (act : 𝓞 E → (Q.A ⟶ Q.A)) (hact : ∀ c, IsMonHom (act c)) {g : ℕ} (u : HolUnif Q.A Q.L g)
    (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P) (hker : ∀ z, z ∈ u.Λ ↔ ∃ a, z = P a)
    (hlin : ∀ (c : 𝓞 E) (s : ℂ) a, u.ex (s • P (c • a)) = u.ex (s • P a) ≫ act c)
    (hW : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (ζ : ℕ → ℂˣ) (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (f : ℕ → D.La → La) (hf : IsTower D EF ζ f) :
    ∃ I : TateIso D ℂ (baseOver (Sp ℂ) ⟶ Q.A) (fun a x => x ≫ act a) (fun n x x' c => WeilIs Q.A Q.L n x x' (unitOn c)),
      I.ζ = ζ ∧ ∀ (n : ℕ) a, I.ev n a = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
  let e : (Fin g → ℂ) → (baseOver (Sp ℂ) ⟶ Q.A) := u.ex
  have eadd : ∀ z w, e (z + w) = e z * e w := u.ex_add
  have eker : ∀ z, e z = 1 ↔ ∃ a, z = P a := fun z => (u.ker z).trans (hker z)
  have epow : ∀ z (n : ℕ), e z ^ n = e (n • z) := fun z n => (ThetaClassical.ex_nsmul u z n).symm
  have e0 : e 0 = 1 := (eker 0).2 ⟨0, (map_zero P).symm⟩
  have hn : ∀ n : ℕ, 0 < n → (n : ℂ) ≠ 0 := fun n h => Nat.cast_ne_zero.2 h.ne'
  have sm : ∀ n : ℕ, 0 < n → ∀ a, (n : ℂ)⁻¹ • P (n • a) = P a := fun n h a => by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  have sm' : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n h z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (hn n h)]
  have md : ∀ n : ℕ, 0 < n → ∀ a b, e ((n : ℂ)⁻¹ • P (a + n • b)) = e ((n : ℂ)⁻¹ • P a) := fun n h a b => by
    rw [map_add, smul_add, eadd, sm n h, (eker _).2 ⟨b, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := ζ, ζ_prim := hp, ζ_pow := hc, ev := fun n a => e ((n : ℂ)⁻¹ • P (f n a)), add := fun n a b => ?_,
            lin := fun n c a => ?_, ker := fun n h a => ?_, onto := fun n h x => ⟨fun hx => ?_, ?_⟩,
            tower := fun n m h h' a => ?_, isom := fun n h a b => ?_ }, rfl, fun _ _ => rfl⟩
  · rcases n.eq_zero_or_pos with rfl | h
    · simp only [Nat.cast_zero, inv_zero, zero_smul, e0, _root_.mul_one]
    · obtain ⟨c, hc⟩ := (hf n h).1 a b
      rw [hc, md n h, map_add, smul_add, eadd]
  · rcases n.eq_zero_or_pos with rfl | h
    · haveI := hact c
      simp only [Nat.cast_zero, inv_zero, zero_smul, e0, MonObj.one_comp]
    · obtain ⟨b, hb⟩ := (hf n h).2.1 c a
      rw [hb, md n h]
      exact hlin c _ _
  · rw [← (hf n h).2.2.1 a, eker]
    refine exists_congr fun b => ⟨fun hb => hinj ?_, fun hb => by rw [hb, sm n h]⟩
    rw [map_nsmul, ← hb, sm' n h]
  · obtain ⟨z, rfl⟩ : ∃ z, e z = x := u.ex_onto x
    rw [epow, eker] at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨a, c, rfl⟩ := (hf n h).2.2.2.1 b
    refine ⟨a, ?_⟩
    rw [← md n h _ c, ← hb, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  · rintro ⟨a, rfl⟩
    rw [epow, sm' n h]
    exact (eker _).2 ⟨_, rfl⟩
  · obtain ⟨b, hb⟩ := (hf n h).2.2.2.2.1 m h' a
    rw [epow, hb, Nat.cast_mul, mul_inv, mul_comm, mul_smul, sm' m h', md n h]
  · exact hW n _ _ _ h ((hf n h).2.2.2.2.2 a b)

theorem exists_log (T : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ (u : ℂ) = eTwoPi w := by
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : (u : ℂ) = eTwoPi (Complex.log u / (2 * Real.pi * Complex.I)) := by
    rw [eTwoPi, mul_div_cancel₀ _ h2, Complex.exp_log u.ne_zero]
  refine ⟨_, ?_, e⟩
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at e
  rw [e, eTwoPi, Complex.norm_exp, Real.exp_lt_exp] at hu
  simp at hu
  have := Real.pi_pos
  nlinarith

theorem of_steps (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (hdict : DictSt) (htow : TowerSt) (hty : TypeSt)
    (hobj : ObjSt) (hth : ThetaSt) (htx : TxSt) : AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := by
  intro E _ _ _ H D R _ _ _ A hρ k β hβ m hm hodd
  letI := H.starRing
  obtain ⟨B, d, hact, hbe, hprim, hth0, hsig⟩ := hdict E H D R A k β hβ
  obtain ⟨f, hf, hrep⟩ := htow E H D R A B d hact
  obtain ⟨g, ty, h, htyp, hh⟩ := hty E H D B (hρ ▸ hsig)
  obtain ⟨-, hbij, hadj, T₁, hT₁⟩ := B.periods_polarised
  obtain ⟨T₂, hT₂⟩ := B.exists_convergence
  have hmem : d.th ∈ B.Theta 1 0 := d.ab.2.2.2.2.2.2.2.1
  obtain ⟨-, hsum, -, hdiff, -⟩ := hT₂ 1 0 d.th hmem
  refine ⟨Real.exp (-(2 * Real.pi * max T₁ T₂)), Real.exp_pos _, fun u hu => ?_⟩
  obtain ⟨w, hw, huw⟩ := exists_log _ u hu
  have hw₁ : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hw₂ : T₂ < w.im := (le_max_right _ _).trans_lt hw
  have hm2 : 0 < m ^ 2 := pow_pos hodd.pos 2
  have hterm := fun x => htx (𝓞 E) A.N B d H.w0 hprim k β hbe m hm hodd w u huw _ _ (hrep _ hm2 x)
  refine ⟨fun x => ?_, ?_⟩
  · refine (d.eX.toEquiv.summable_iff (f := fun χ : A.N.X => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖)).1 ?_
    exact ((hsum w hw₂ ((m : ℂ)⁻¹ • B.Pw w (f (m ^ 2) x))).mul_left _).congr fun y =>
      (norm_mul _ _).symm.trans (congrArg norm (hterm x y).symm)
  obtain ⟨-, -, hlin, -, hspan, -, -, -, hper⟩ := hT₁ w hw₁
  let P : B.La →+ (Fin g → ℂ) := h.toLinearMap.toAddMonoidHom.comp (B.Pw w)
  obtain ⟨hinj, hdisc, hsp, Hm, hherm, hpos, him⟩ := hper g h P fun _ => rfl
  have hPlin : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x i =>
    (congrArg (fun v => h v i) (hlin a x)).trans (hh a _ i)
  obtain ⟨Q, oa, U, Hm', χ, F, hΛ, hpr, hdet, hAH, hΛ', him', hχ, hex, hW⟩ :=
    hobj E H D B.La B.EF g ty P Hm htyp hbij hadj hPlin hinj hdisc hsp hherm hpos him
  let P' : B.La →+ (Fin Q.g → ℂ) := F.toLinearMap.toAddMonoidHom.comp P
  obtain ⟨I, hI, hev⟩ := exists_tateIso D B.EF Q oa.act oa.hom U P' (F.injective.comp hinj)
    (fun z => ⟨hΛ' z, fun ⟨a, ha⟩ => ha ▸ hΛ a⟩) (fun c s a => by
      have := hex c (s • P a)
      rw [map_smul] at this
      refine Eq.trans (congrArg U.ex ?_) this
      refine (map_smul F s _).symm.trans (congrArg F (funext fun i => ?_))
      simp only [Pi.smul_apply, hPlin, smul_eq_mul]
      ring) hW A.I.ζ A.I.ζ_prim A.I.ζ_pow f hf
  have hS : Differentiable ℂ (B.Sum 1 0 d.th w) := fun v =>
    ((hdiff.differentiableAt ((isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).mem_nhds
      (show T₂ < ((w, v) : ℂ × B.V).1.im from hw₂))).comp v
      ((differentiableAt_const w).prodMk differentiableAt_id) :)
  obtain ⟨Θ, hΘ, hΘ0, hΘp, hΘv⟩ := hth (𝓞 E) B H.w0 hprim d.th hmem w hS Q.g (h.trans F) Hm' hAH.1 hspan him'
  have hne : Θ ≠ 0 := by
    obtain ⟨v, hv⟩ := B.exists_Sum_ne_zero one_ne_zero 0 hth0 (w := w) fun z => (hsum w hw₂ _).of_norm
    exact fun e => hv ((hΘ0 v).1 (congrFun e _))
  have hfn : U.IsThetaFn Hm' χ 1 Θ := ⟨hΘ, fun l z => by
    obtain ⟨l, hl⟩ := l
    obtain ⟨a, rfl⟩ := hΛ' l hl
    rw [pow_one, hχ]
    exact hΘp a z⟩
  refine ⟨⟨Q, oa, hpr, H.rt0, H.sqrt_neg_disc_sq, hdet, I, inferInstance⟩, rfl, congrFun hI _, ?_⟩
  have key := isThetaPt_classical hL hL2 hT Q U Hm' χ Θ m (I.ev (m ^ 2)) (fun x => ⟨F (P (f _ x)), hΛ _⟩) hodd hAH hfn hne
    fun x => by rw [hev, Nat.cast_pow]; rfl
  refine Eq.mp (congrArg (IsThetaPt Q m (I.ev (m ^ 2))) (funext fun x => congrArg fnOf ?_)) key
  rw [hχ, _root_.mul_assoc]
  refine (congrArg (_ * ·) (hΘv _ m hodd.pos.ne')).trans ?_
  rw [← _root_.mul_assoc, AnArc.Sum, ← tsum_mul_left]
  exact (tsum_congr fun y => (hterm x y).symm).trans
    (d.eX.toEquiv.tsum_eq fun χ : A.N.X => (A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ)

theorem exists_full_of_small : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := fun hV _ _ _ _ _ hT =>
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  have hF : BrFamSt := _root_.GlobalTheory.Ex.brFam hL hL2
  of_steps hL hL2 hT
    (_root_.GlobalTheory.Ex.Arch.dict_of_val (_root_.GlobalTheory.ActValues.brAct hL) (_root_.GlobalTheory.Ex.Arch.AbVal.valSt hL hF (_root_.GlobalTheory.Ex.Arch.FibEx.fibEx hL hT) _root_.GlobalTheory.Ex.Arch.fibGrp (_root_.GlobalTheory.Ex.Arch.fibCubeSt hL) (_root_.GlobalTheory.Ex.Arch.FibSym.fibSymSt hL)
      (_root_.GlobalTheory.Ex.Arch.FibRos.fibRosSt hL) (_root_.GlobalTheory.Ex.Arch.FibPrim.fibPrim_of_laws hL) _root_.GlobalTheory.Ex.Arch.fibSec (_root_.GlobalTheory.Ex.Arch.fibLie_of_laws hL)))
    (_root_.GlobalTheory.Ex.Arch.towerSt_of _root_.GlobalTheory.Ex.GtValues.points_correspond (_root_.GlobalTheory.WeilValues.weil_eq_values _root_.GlobalTheory.Ex.GtValues.points_correspond hF) _root_.GlobalTheory.Ex.Arch.ptSt (_root_.GlobalTheory.Ex.Arch.qkSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt) _root_.GlobalTheory.Ex.Arch.Wp.wp_eq)
    _root_.GlobalTheory.Ex.Arch.typeSt (_root_.GlobalTheory.Ex.Arch.objSt_of_triple_reframe hL (_root_.GlobalTheory.Ex.Arch.tripleSt_of_laws hL hT) (_root_.GlobalTheory.Ex.Arch.reframe hT)) _root_.GlobalTheory.Ex.Arch.theta_sum_appellHumbert (_root_.GlobalTheory.Ex.Arch.txSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt)

end GlobalTheory.Ex.Arch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusExtensionParameterGenericFibrePoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_parAt : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a : u.PtC), ∃ g, u.ParAt S.N a g := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l a
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h1 : 2 ≤ ρ.n ^ ρ.k := le_trans ρ.n_prime.two_le
      (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    nlinarith
  haveI : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  obtain ⟨k, hk, hint⟩ := GlobalTheory.T.theta_test_power_integral hL o Ω S ρ p y₀ u a
  obtain ⟨a₁, ⟨c, hc, hca⟩, hpow⟩ := GlobalTheory.T.exists_integral_nthRoot_testModel_point hL o Ω S ρ p y₀ u (a ^ k) k hk hint
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.exists_torusExtensionPoint_of_integralModelPoint hL o Ω S ρ p y₀ u c hc
  have hpar := (GlobalTheory.T.torusCoord_unit_and_section_eq_expansion hL o Ω S ρ p y₀ u c g₁ a₁ hc hca hg₁).2
  have hNk : 1 ≤ S.N * k := Nat.mul_pos (by omega) hk
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.N * k) hNk
  haveI : IsMonHom u.U.gen.hom := u.U.gen_hom
  have hk' : (a₁ ≫ u.U.gen.hom) ^ k = (a ≫ u.U.gen.hom) ^ k := by
    rw [← MonObj.pow_comp, ← MonObj.pow_comp, hpow]
  have hx : ((a ≫ u.U.gen.hom) * (a₁ ≫ u.U.gen.hom)⁻¹) ^ (S.N * k) = 1 := by
    rw [mul_comm S.N k, pow_mul, mul_pow, inv_pow, hk', mul_inv_cancel, one_pow]
  obtain ⟨pk, hpk⟩ := hsurj _ hx
  obtain ⟨g, hg⟩ := (gt_add_iota_sub_exist hL o Ω S ρ p y₀ u).1 pk.g g₁
  refine ⟨g, GlobalTheory.T.thetaParameter_of_thetaParameter_mul_degree hL o Ω S ρ p y₀ u l S.N k a g hN hk ?_⟩
  exact ParTranslate.parAt_translate hL o Ω S ρ p y₀ u (S.N * k) pk _ a₁ a g₁ g hNk
    ((hf pk _).2 hpk.symm) (by rw [inv_mul_cancel_right]) hg (hpar _ hNk)

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrimeStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_completeLocalDomain_prime : Laws → Laws2 → Laws3 → Ega → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → SplitOver G I → ThetaNZ G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegData R I) (U : Unif I D A G), U.LG = P.L ∧ U.gen = gen := by
  first | exact @GlobalTheory.PrimeUnif.exists_unif | exact GlobalTheory.PrimeUnif.exists_unif | (intros; apply GlobalTheory.PrimeUnif.exists_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVeryAmplePowerStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_very_ample_power : ∀ (A : Type) [CommRing A] (X : Over (Spec (CommRingCat.of A))) (L : LB X.left), L.IsLB → RelAmple X L → ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (g₀ : A →+* K) (X₀ : Scheme.{0}) (π : X₀ ⟶ X.left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ X.hom (Spec.map (CommRingCat.ofHom g₀)) → ∃ d : ℕ, 1 ≤ d ∧ FirstCohomologyVanishes ((pw L d).pull π) ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (pw L d)), VeryAmpleBy X.hom (pw L d) s := by
  first | exact @GlobalTheory.Algebraise.exists_veryAmple_h1Zero_pull | exact GlobalTheory.Algebraise.exists_veryAmple_h1Zero_pull | (intros; apply GlobalTheory.Algebraise.exists_veryAmple_h1Zero_pull <;> assumption)
end

