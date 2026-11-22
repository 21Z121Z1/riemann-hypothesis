import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsCokerIsoTr
import Development.AutomorphicArithmetic.DivisorFrames.VectorBundleSubbundleUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctorialLiftsOfObstructionTwoZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_isFun_of_isOb2_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → Module.Projective R₀ (GlobForm s₀) → ∀ L : Pre I π (OAff s₀), (∀ w, L.IsOb2 α w 0) → ∃ L' : Pre I π (OAff s₀), L'.IsFun := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hpar hproj L hob

  obtain ⟨θ, -, -, hθ, -⟩ := hob 0

  let Wm : Submodule R (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') :=
    { carrier := {g | ∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))}
      add_mem' := fun hx hy T T' a ↦ Ideal.add_mem _ (hx T T' a) (hy T T' a)
      zero_mem' := fun T T' a ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg T T' a ↦ by
        show r • g T T' a ∈ _
        rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hg T T' a) }
  let q : (∀ (T T' : AffOp X₀) (_ : T ⟶ T'), L.B T') →ₗ[R]
      (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun g T T' T'' a b ↦ L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b
      map_add' := fun g g' ↦ by
        funext T T' T'' a b
        simp only [Pi.add_apply, map_add]; abel
      map_smul' := fun r g ↦ by
        funext T T' T'' a b
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_sub, smul_add] }
  let v : GlobForm s₀ →+ (∀ (T T' T'' : AffOp X₀) (_ : T ⟶ T') (_ : T' ⟶ T''), L.B T'') :=
    { toFun := fun w T T' T'' a b ↦ θ T T' T'' a b (w.1 T)
      map_zero' := by funext T T' T'' a b; simp
      map_add' := fun w w' ↦ by funext T T' T'' a b; simp }
  have hv : ∀ (r : R) (w : GlobForm s₀), v (π r • w) = r • v w := by
    intro r w
    funext T T' T'' a b
    show θ T T' T'' a b (π r • w.1 T) = r • θ T T' T'' a b (w.1 T)
    have e : π r • w.1 T = L.p T (algebraMap R (L.B T) r) • w.1 T := by
      rw [SemiHom.map_algebraMap (L.semi T), algebraMap_smul]
    rw [e, (hθ T T' T'' a b).smul, AlgHom.commutes, ← Algebra.smul_def]
  have hW : ∀ (r : R), π r = 0 → ∀ m ∈ Wm, r • m = 0 := by
    intro r hr m hm
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    funext T T' a
    show r • m T T' a = 0
    rw [Algebra.smul_def]
    exact mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem _ hrI) (hm T T' a)
  have hex : ∀ w : GlobForm s₀, ∃ m ∈ Wm, q m = v w := by
    intro w
    obtain ⟨g, hg, hgθ⟩ := GlobalTheory.T.exists_defect_coboundary_of_obstructionClass_zero R R₀ I hI π hπ hk R₁ α _ (OAff s₀) L w θ hθ (hob w)
    refine ⟨g, hg, ?_⟩
    funext T T' T'' a b
    exact (hgθ T T' T'' a b).symm
  obtain ⟨u, hus, huW, huq⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hproj _ _ Wm hW q v hv hex

  have hext : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃! ξ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T',
      (∀ b w, ξ (L.p T b • w) = L.ρ a b * ξ w) ∧ (∀ w, ξ w ∈ I.map (algebraMap R (L.B T'))) ∧
        ∀ w : GlobForm s₀, ξ (w.1 T) = u w T T' a := fun T T' a ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar T _ _ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)
      ((Pi.evalAddMonoidHom (fun _ ↦ L.B T') a).comp ((Pi.evalAddMonoidHom _ T').comp ((Pi.evalAddMonoidHom _ T).comp u)))
      (fun r w ↦ by
        show u (π r • w) T T' a = r • u w T T' a
        rw [hus]; rfl) (fun w ↦ huW w T T' a)
  choose ξ hξ huniq using hext
  have hβ : ∀ (T T' : AffOp X₀) (a : T ⟶ T'), ∃ β : L.B T →ₐ[R] L.B T', IsTheta I (L.p T) (L.ρ a) β (ξ T T' a) :=
    fun T T' a ↦ (theta_classify R R₀ _ _ _ I hI π hπ (L.p T) (L.semi T) (L.surj T) (L.ker T) (L.ρ a)).2
      (ξ T T' a) (hξ T T' a).1 (hξ T T' a).2.1
  choose ρ' hρ' using hβ
  have hρ'e : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, ρ' T T' a x = L.ρ a x - ξ T T' a (D R₀ _ (L.p T x)) := by
    intro T T' a x
    rw [(hρ' T T' a).der]; abel
  have hp0 : ∀ (T T' : AffOp X₀) (a : T ⟶ T') y, L.p T' (ξ T T' a y) = 0 :=
    fun T T' a y ↦ (L.ker T' _).2 ((hξ T T' a).2.1 y)
  have hnat : ∀ (T T' : AffOp X₀) (a : T ⟶ T') x, L.p T' (ρ' T T' a x) = mp (OAff s₀) a (L.p T x) := by
    intro T T' a x
    rw [hρ'e, map_sub, hp0, sub_zero, L.nat]
  let L' : Pre I π (OAff s₀) :=
    { B := L.B, p := L.p, semi := L.semi, surj := L.surj, ker := L.ker, smooth := L.smooth
      ρ := fun {T T'} a ↦ ρ' T T' a
      nat := fun {T T'} a x ↦ hnat T T' a x }
  refine ⟨L', ?_⟩

  have hcomp : ∀ (T T' T'' : AffOp X₀) (a : T ⟶ T') (b : T' ⟶ T'') (y : Ω[Sec s₀ T.unop.1⁄R₀]),
      ξ T T'' (a ≫ b) y = L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y := by
    intro T T' T'' a b
    let ψ : Ω[Sec s₀ T.unop.1⁄R₀] →+ L.B T'' :=
      AddMonoidHom.mk' (fun y ↦ L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
        (fun y z ↦ by simp only [map_add]; abel)
    have hψm : ∀ y, ψ y ∈ I.map (algebraMap R (L.B T'')) := fun y ↦
      Ideal.sub_mem _ (Ideal.add_mem _ (algHom_mem_map I (L.ρ b) ((hξ T T' a).2.1 y)) ((hξ T' T'' b).2.1 _))
        ((hθ T T' T'' a b).mem y)
    have e : ψ = ξ T T'' (a ≫ b) := by
      refine huniq T T'' (a ≫ b) ψ ⟨fun c y ↦ ?_, hψm, fun w ↦ ?_⟩
      · have h1 : ψ (L.p T c • y) = L.ρ b (L.ρ a c) * ψ y := by
          show L.ρ b (ξ T T' a (L.p T c • y)) + ξ T' T'' b (p1 (OAff s₀) a (L.p T c • y)) -
              θ T T' T'' a b (L.p T c • y) = L.ρ b (L.ρ a c) * (L.ρ b (ξ T T' a y) + ξ T' T'' b (p1 (OAff s₀) a y) - θ T T' T'' a b y)
          rw [(hξ T T' a).1, oneFormsMapOfFunctorMorphism_smul, ← L.nat, (hξ T' T'' b).1, (hθ T T' T'' a b).smul, map_mul]
          simp only [AlgHom.comp_apply]; ring
        have h2 : L.ρ b (L.ρ a c) = L.ρ (a ≫ b) c + θ T T' T'' a b (D R₀ _ (L.p T c)) := by
          rw [(hθ T T' T'' a b).der]; simp
        rw [h1, h2, add_mul, mul_eq_zero_of_mem_map hI ((hθ T T' T'' a b).mem _) (hψm y), add_zero]
      · show L.ρ b (ξ T T' a (w.1 T)) + ξ T' T'' b (p1 (OAff s₀) a (w.1 T)) - θ T T' T'' a b (w.1 T) = u w T T'' (a ≫ b)
        rw [← w.2 a, (hξ T T' a).2.2, (hξ T' T'' b).2.2]
        have := congrFun (congrFun (congrFun (congrFun (congrFun (huq w) T) T') T'') a) b
        change L.ρ b (u w T T' a) - u w T T'' (a ≫ b) + u w T' T'' b = θ T T' T'' a b (w.1 T) at this
        rw [← this]; abel
    intro y
    rw [← e]; rfl
  intro T T' T'' a b x
  change ρ' T T'' (a ≫ b) x = ρ' T' T'' b (ρ' T T' a x)
  have hD : D R₀ _ (L.p T' (ρ' T T' a x)) = p1 (OAff s₀) a (D R₀ _ (L.p T x)) := by
    rw [hnat, p1_D]
  rw [hρ'e T' T'' b, hD, hρ'e T T' a, map_sub, hρ'e, hcomp]
  have h2 : L.ρ b (L.ρ a x) = L.ρ (a ≫ b) x + θ T T' T'' a b (D R₀ _ (L.p T x)) := by
    rw [(hθ T T' T'' a b).der]; simp
  rw [h2]; abel

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section
namespace GlobalTheory.Poinc.FieldConj
open GlobalTheory.Points RatModel
open scoped Pointwise

theorem eq_of_val_eq_fibre {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {X : Scheme.{0}}
    (q : M.Z ⟶ X) [IsAffineHom q] {K : Type} [Field K] (y y' : Sp K ⟶ M.Z) (hyy : y ≫ q = y' ≫ q)
    (h : ∀ b ∈ M.ringOn {z | q z = (y ≫ q) (IsLocalRing.closedPoint K)}, M.val y b = M.val y' b) : y = y' := by
  set x := (y ≫ q) (IsLocalRing.closedPoint K) with hx
  have hxz : q (y (IsLocalRing.closedPoint K)) = x := rfl
  have hxz' : q (y' (IsLocalRing.closedPoint K)) = x := by rw [hx, hyy]; rfl
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hsub : ∀ a ∈ M.ringOn (q ⁻¹ᵁ V : Set M.Z), a ∈ M.ringOn {z | q z = x} := fun a ha =>
    M.ringOn_anti (fun z (hz : q z = x) => show q z ∈ V by rw [hz]; exact hxV) ha
  have hzU : y (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz]; exact hxV
  have hzU' : y' (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz']; exact hxV
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)

  have hinv : ∀ {w : Sp K ⟶ M.Z} (hw : Set.range w = {w (IsLocalRing.closedPoint K)}) {a : Ω},
      a ∈ M.O (w (IsLocalRing.closedPoint K)) → a ≠ 0 → (a⁻¹ ∈ M.O (w (IsLocalRing.closedPoint K)) ↔ M.val w a ≠ 0) := by
    intro w hw a ha h0
    rw [val_ne_zero_iff hw ⟨a, ha⟩, isUnit_O_iff]
    exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
  have hpt : y (IsLocalRing.closedPoint K) = y' (IsLocalRing.closedPoint K) := by
    refine GlobalTheory.Points.point_eq_of_inv_mem_iff o Ω M _ hU _ _ hzU hzU' fun a ha h0 => ?_
    rw [hinv hr (M.ringOn_le_O hzU ha) h0, hinv hr' (M.ringOn_le_O hzU' ha) h0, h a (hsub a ha)]
  set z := y (IsLocalRing.closedPoint K) with hz
  have hO : ∀ a ∈ M.O z, M.val y a = M.val y' a := by
    intro a ha
    obtain ⟨c, hc, d, hd, hd0, hdi, rfl⟩ :=
      GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine o Ω M _ hU z hzU a ha
    have hsp : ∀ w, y w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
    have hsp' : ∀ w, y' w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K), hpt]
    have hcz := M.ringOn_le_O hzU hc
    have hdz := M.ringOn_le_O hzU hd
    have hq : c / d ∈ M.O z := ha
    have e1 := val_mul hsp hq hdz
    have e1' := val_mul hsp' hq hdz
    rw [div_mul_cancel₀ c hd0] at e1 e1'
    have hne : M.val y d ≠ 0 := (hinv hr hdz hd0).1 hdi
    have hne' : M.val y' d ≠ 0 := by rw [← h d (hsub d hd)]; exact hne
    rw [eq_div_of_mul_eq hne e1.symm, eq_div_of_mul_eq hne' e1'.symm, h c (hsub c hc), h d (hsub d hd)]
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local hpt fun W h₁ h₂ => ?_
  have hW : z ∈ W := h₁ (x := IsLocalRing.closedPoint K) trivial
  ext f
  have e1 := val_valF ((top_le_preimage_iff y W).1 h₁) f
  have e2 := val_valF ((top_le_preimage_iff y' W).1 h₂) f
  have e3 := hO _ (valF_mem_O hW f)
  rw [e1, e2] at e3
  unfold valF at e3
  rw [dif_pos h₁, dif_pos h₂] at e3
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e3

theorem galConj : ∀ (A F L K : Type) [CommRing A] [IsDomain A] [Field F] [Field L] [Field K] [CharZero K] [Algebra A F] [IsFractionRing A F] [IsIntegrallyClosed A] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [IsGalois F L] (B : Subring L), (∀ b : L, b ∈ B ↔ IsIntegral A b) → ∀ e e' : B →+* K, (∀ b : B, (∃ a : A, algebraMap A L a = b) → e b = e' b) → ∃ σ : L ≃ₐ[F] L, ∀ b c : B, (c : L) = σ b → e' b = e c := by
  intro A F L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ B hB e e' hA
  classical
  have hσB : ∀ (σ : L ≃ₐ[F] L) (b : L), b ∈ B → σ b ∈ B := fun σ b hb =>
    (hB _).2 (IsIntegral.map ((σ : L →ₐ[F] L).restrictScalars A) ((hB b).1 hb))
  let σB : (L ≃ₐ[F] L) → B →+* B := fun σ =>
    ((σ : L →+* L).comp B.subtype).codRestrict B fun b => hσB σ b b.2
  have hσB_apply : ∀ σ (b : B), ((σB σ b : B) : L) = σ b := fun _ _ => rfl

  have claim : ∀ b : B, ∃ σ : L ≃ₐ[F] L, e' b = e (σB σ b) := by
    intro b
    let P : Polynomial B := ∏ σ : L ≃ₐ[F] L, (Polynomial.X - Polynomial.C (σB σ b))
    have hPmap : ∀ τ : L ≃ₐ[F] L, (P.map B.subtype).map (τ : L →+* L) = P.map B.subtype := by
      intro τ
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
      rfl
    have hcoeff : ∀ n, ∃ a : A, algebraMap A L a = (P.coeff n : L) := by
      intro n
      have hfix : ∀ τ : L ≃ₐ[F] L, τ (P.coeff n : L) = P.coeff n := by
        intro τ
        have := congrArg (fun p => Polynomial.coeff p n) (hPmap τ)
        simpa [Polynomial.coeff_map] using this
      obtain ⟨f, hf⟩ := (IsGalois.mem_bot_iff_fixed (P.coeff n : L)).2 hfix
      change algebraMap F L f = _ at hf
      have hint : IsIntegral A (algebraMap F L f) := by rw [hf]; exact (hB _).1 (P.coeff n).2
      have hint' : IsIntegral A f := by
        rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A F L) (algebraMap F L).injective]
        exact hint
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
      exact ⟨a, by rw [IsScalarTower.algebraMap_apply A F L, ha, hf]⟩
    have hmap : P.map e = P.map e' := by
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      obtain ⟨a, ha⟩ := hcoeff n
      exact hA _ ⟨a, ha⟩
    have h0 : (P.map e').eval (e' b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [sub_eq_zero]; exact Subtype.ext rfl), map_zero]
    rw [← hmap] at h0
    simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h0
    obtain ⟨σ, -, hσ⟩ := Finset.prod_eq_zero_iff.1 h0
    exact ⟨σ, sub_eq_zero.1 hσ⟩
  let H : (L ≃ₐ[F] L) → AddSubgroup B := fun σ =>
    (e'.toAddMonoidHom - (e.comp (σB σ)).toAddMonoidHom).ker
  have hmemH : ∀ σ (b : B), b ∈ H σ ↔ e' b = e (σB σ b) := fun σ b => by
    simp [H, AddMonoidHom.mem_ker, sub_eq_zero]
  have hcover : ⋃ σ ∈ (Finset.univ : Finset (L ≃ₐ[F] L)), (0 : B) +ᵥ ((H σ : AddSubgroup B) : Set B) = Set.univ := by
    refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨σ, hσ⟩ := claim b
    refine Set.mem_iUnion₂.2 ⟨σ, Finset.mem_univ _, ?_⟩
    rw [zero_vadd]
    exact (hmemH σ b).2 hσ
  obtain ⟨σ, -, hfin⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcover
  refine ⟨σ, fun b c hc => ?_⟩
  have hcσ : c = σB σ b := Subtype.ext hc
  subst hcσ
  have hn : (H σ).index ≠ 0 := hfin.index_ne_zero
  have hmem := (hmemH σ _).1 (AddSubgroup.nsmul_index_mem (H σ) b)
  rw [map_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hmem
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) hmem

theorem val_algebraMap_of_comp {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
    [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z}
    (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {K : Type} [Field K] (y : Sp K ⟶ M₂.Z) {x : Ω₁}
    (hx : x ∈ M₁.O ((y ≫ q) (IsLocalRing.closedPoint K))) :
    M₂.val y (algebraMap Ω₁ Ω₂ x) = M₁.val (y ≫ q) x := by
  obtain ⟨U, f, hzU, rfl⟩ := hx
  have h1 : Set.range (y ≫ q) ⊆ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  have h2 : Set.range y ⊆ q ⁻¹ᵁ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  rw [← GlobalTheory.Poinc.FinPts.valF_app hg ⟨_, hzU⟩ f, val_valF h2, val_valF h1]
  exact (valR_comp y q U f).symm

theorem exists_aut_eq_of_comp_eq : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ _ _ M₁ M₂ q hN₁ hN₂ hF hg K _ _ y y' hyy
  set z₁ := (y ≫ q) (IsLocalRing.closedPoint K) with hz₁
  haveI : IsIntegrallyClosed (M₁.O z₁) := isIntegrallyClosed_O hN₁ z₁
  let B : Subring Ω₂ := (M₂.ringOn {z | q z = z₁}).toSubring
  have hB : ∀ b : Ω₂, b ∈ B ↔ IsIntegral (M₁.O z₁) b := by
    intro b
    letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
    have h1 := (GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg z₁).1 b
    have h2 : IsIntegral (M₁.Z.presheaf.stalk z₁) b ↔ IsIntegral (M₁.O z₁) b := by
      constructor
      · intro hb
        exact IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).toRingHom (RingHom.id Ω₂) (RingHom.ext fun _ => rfl) hb
      · intro hb
        refine IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).symm.toRingHom (RingHom.id Ω₂) (RingHom.ext fun x => ?_) hb
        show algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ ((M₁.stalkEquiv z₁).symm x)) = algebraMap Ω₁ Ω₂ (x : Ω₁)
        rw [← coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [← h2, ← mem_integralClosure_iff, h1, Subalgebra.mem_toSubring, mem_ringOn]
    rfl
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)
  have hz : q (y (IsLocalRing.closedPoint K)) = z₁ := rfl
  have hz' : q (y' (IsLocalRing.closedPoint K)) = z₁ := by rw [hz₁, hyy]; rfl
  let e : B →+* K := (M₂.valHom y _ hr).comp
    (Subring.inclusion (show B ≤ (M₂.O (y (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz))
  let e' : B →+* K := (M₂.valHom y' _ hr').comp
    (Subring.inclusion (show B ≤ (M₂.O (y' (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz'))
  have he : ∀ b : B, e b = M₂.val y b := fun _ => rfl
  have he' : ∀ b : B, e' b = M₂.val y' b := fun _ => rfl
  have hA : ∀ b : B, (∃ a : M₁.O z₁, algebraMap (M₁.O z₁) Ω₂ a = b) → e b = e' b := by
    rintro b ⟨a, hab⟩
    rw [he, he', ← hab]
    show M₂.val y (algebraMap Ω₁ Ω₂ a) = M₂.val y' (algebraMap Ω₁ Ω₂ a)
    rw [val_algebraMap_of_comp hg y a.2, val_algebraMap_of_comp hg y' (by rw [← hyy]; exact a.2), hyy]
  obtain ⟨σ, hσ⟩ := galConj (M₁.O z₁) Ω₁ Ω₂ K B hB e e' hA
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.Poinc.GalAut.autAct o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg σ
  haveI := hF
  have key : y ≫ s = y' := by
    refine eq_of_val_eq_fibre M₂ q (y ≫ s) y' (by rw [Category.assoc, hs2, hyy]) fun b hb => ?_
    have hys : (y ≫ s) ≫ q = y ≫ q := by rw [Category.assoc, hs2]
    rw [hys] at hb
    have hbB : b ∈ B := hb
    have hσB : σ b ∈ B := (hB _).2
      (IsIntegral.map ((σ : Ω₂ →ₐ[Ω₁] Ω₂).restrictScalars (M₁.O z₁)) ((hB b).1 hbB))
    rw [hs3]
    exact (hσ ⟨b, hbB⟩ ⟨σ b, hσB⟩ rfl).symm
  refine ⟨σ, s, hs1, key, fun b => ?_⟩
  rw [← key]
  exact hs3 K y b

end GlobalTheory.Poinc.FieldConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.GenRestrict

theorem unifPre_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) :
    IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧
      LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) := by
  have := U.gen_hom
  refine ⟨?_, ?_⟩
  · have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  · have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hext : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))) := U.ext
    have h1 : LBIso (A.L.pull (U.gen.inv.left ≫ U.gen.hom.left))
        (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame A.L _ (fun _ => U.gen.hom.left) _ U.gen.inv.left fun _ => rfl)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull A.L _ hgi)
      (chartPullSame U.LG.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem weilIs_congr_base {S X : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (k : ℤ) {a b : X ⟶ S}
    (hab : a = b) (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(X, ⊤)ˣ) : WeilIs G L k x y c ↔ WeilIs G L k x' y' c := by
  subst hab
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  exact Iff.rfl

end GlobalTheory.GenRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrassmannianPairBundle
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB
theorem _root_.GlobalTheory.T.exists_grassmannian_pair_bundle : ∀ (B : Scheme.{0}) (E : B.Modules) (n m₁ m₂ : ℕ), GlobalTheory.VB.IsVB E n → m₁ ≤ m₂ → m₂ ≤ n →
    ∃ (G : Scheme.{0}) (γ : G ⟶ B) (S P : G.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback γ).obj E),
      GlobalTheory.VB.IsVB S m₁ ∧ GlobalTheory.VB.IsVB P m₂ ∧ GlobalTheory.VB.IsSubbundle s ∧ GlobalTheory.VB.IsSubbundle j ∧
      GlobalTheory.VB.IsVB (Limits.cokernel j) (n - m₂) ∧ GlobalTheory.OmitFlag.IsPairBundle γ E m₁ m₂ s j :=
  UpperTheory.vector_bundle_subbundle_universal UpperTheory.Grass.exists_grass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantFormsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left) (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1), (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1), (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧ ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  first | exact @GlobalTheory.InvForm.exists_transl_val | exact GlobalTheory.InvForm.exists_transl_val | (intros; apply GlobalTheory.InvForm.exists_transl_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalvingPointAbelianSchemeFiniteExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_halving_point_abelianScheme_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (a : 𝟙_ (Over (Sp R)) ⟶ B), IsCN R → IsAbelianScheme B → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (b : Over.mk (spMap ρ) ⟶ B), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ b ^ 2 = toUnit _ ≫ a := by
  first | exact @GlobalTheory.HalfPt.exists_half_point | exact GlobalTheory.HalfPt.exists_half_point | (intros; apply GlobalTheory.HalfPt.exists_half_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolyLocalInvariantNonposChar0Statement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → ∀ e k : ℕ, 0 < e → GlobalTheory.FactorDepth.nuLocOf C e k (MvPolynomial.map io P₁) ≤ 0 := by
  first | exact @GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos | exact GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos | (intros; apply GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFractionFiniteNormalCover
section
open AlgebraicGeometry CategoryTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Geo.Tor

open GlobalTheory.Poinc.FinPts in

theorem GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (z₁ : M₁.Z) (z₂ : M₂.Z), q z₂ = z₁ → letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q _ hF hg z₁ z₂ hq x hx
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) := fun _ => rfl
  haveI := hF
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := z₁) trivial
  have hz₂ : z₂ ∈ q ⁻¹ᵁ U := show q z₂ ∈ U by rw [hq]; exact hz
  obtain ⟨c, hc, d, hd, hd0, hdinv, e⟩ := GlobalTheory.T.exists_fraction_ringOn_of_mem_modelLocalRing _ _ M₂ _ (hU.preimage q) z₂ hz₂ x hx
  exact ⟨c, (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hc), d,
    (mem_integralClosure_iff _ _).2 (isIntegral_of_mem_ringOn hF hg halg hU hz hd), hd0, hdinv, e⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftObstructionStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleLiftObstruction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  first | exact @GlobalTheory.LBObs.ObEx.exists_isObL | exact GlobalTheory.LBObs.ObEx.exists_isObL | (intros; apply GlobalTheory.LBObs.ObEx.exists_isObL <;> assumption)
end

