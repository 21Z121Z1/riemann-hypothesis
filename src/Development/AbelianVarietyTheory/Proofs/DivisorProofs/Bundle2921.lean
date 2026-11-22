import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.BaseTerms

def FrPull {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    {A : PolAV (Sp (FractionRing V))} {A₂ : PolAV (Sp (FractionRing V'))} {ψ : A₂.A.left ⟶ A.A.left}
    (w : LB.Iso A₂.L (A.L.pull ψ)) (f : FractionRing V →+* FractionRing V')
    (x₂ : TFK (R := V') (FractionRing V') ⟶ A₂.A) (fr₂ : FrAt x₂) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x)
    (ρ : FractionRing V') : Prop :=
  ∀ (z : (TFK (R := V') (FractionRing V')).left) (J : ((TFK (R := V') (FractionRing V')).left ⟶ A.A.left) → A.L.ι)
    (J' : ((TFK (R := V') (FractionRing V')).left ⟶ A₂.A.left) → A₂.L.ι), Good A.L z J → Good A₂.L z J' →
    ((gw w x₂.left z (J (x₂.left ≫ ψ)) (J' x₂.left) : _) * (val fr₂ (𝟙 _) z J' : _) : ((TFK (R := V') (FractionRing V')).left.presheaf.stalk z)) =
      @id ((TFK (R := V') (FractionRing V')).left.presheaf.stalk z) (GlobalTheory.UT.cst (R := V') (FractionRing V') z ρ) *
        (val fr (show (TFK (R := V') (FractionRing V')).left ⟶ (TFK (R := V) (FractionRing V)).left from spMap f) z J : _)

end GlobalTheory.Poinc.Sep.BaseTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁]

theorem exists_basis (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) :
    letI := ρ₁.toAlgebra; ∃ B : Module.Basis (Fin d) R R₁, ⇑B = b := by
  letI := ρ₁.toAlgebra
  have hs : ∀ (c : R) (x : R₁), c • x = ρ₁ c * x := fun c x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent R b := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    have h1 : (0 : R₁) = ∑ l, ρ₁ (g l) * b l := by
      rw [← hg]; simp only [hs]
    have h2 : (0 : R₁) = ∑ l, ρ₁ ((0 : Fin d → R) l) * b l := by simp
    exact congrFun ((hb 0).unique h1 h2) i
  refine ⟨Module.Basis.mk hli ?_, Module.Basis.coe_mk _ _⟩
  intro r _
  obtain ⟨c, hc, -⟩ := hb r
  rw [hc]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← hs]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem gs_zero0 {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

variable {X Z : Scheme.{0}}

theorem aff_coeff (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    {V : X.Opens} (hV : IsAffineOpen V) :
    (∀ t : Γ(Z, q ⁻¹ᵁ V), ∃ a : Fin d → Γ(X, V),
      t = ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l)) ∧
    (∀ a : Fin d → Γ(X, V), ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l) = 0 → a = 0) := by
  classical
  letI := ρ₁.toAlgebra
  obtain ⟨B, hB⟩ := exists_basis ρ₁ b hb
  have hg : ρ₁.Flat := by
    have : Module.Free R R₁ := Module.Free.of_basis B
    exact (inferInstance : Module.Flat R R₁)
  letI : Algebra R Γ(X, V) := (GlobalTheory.AbLaw.cst f V).toAlgebra
  obtain ⟨e, he⟩ := GlobalTheory.FlatSec.exists_equiv_of_isPushout (R := R) (q.app V) (GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V))
    (GlobalTheory.FlatSec.isPushout_app hg H hV.isCompact hV.isQuasiSeparated)
  have hsum : ∀ a : Fin d → Γ(X, V), e (∑ l, B l ⊗ₜ[R] a l) =
      ∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l) := by
    intro a; rw [map_sum]; simp only [he, hB]
  constructor
  · intro t
    refine ⟨fun l => TensorProduct.equivFinsuppOfBasisLeft B (e.symm t) l, ?_⟩
    rw [← hsum]
    have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply B (TensorProduct.equivFinsuppOfBasisLeft B (e.symm t))
    rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    rw [← h, AddEquiv.apply_symm_apply]
  · intro a ha
    rw [← hsum] at ha
    have h0 : ∑ l, B l ⊗ₜ[R] a l = 0 := e.injective (ha.trans (map_zero e).symm)
    funext k
    have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft B w k) h0
    simpa [map_sum, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self,
      Finsupp.single_apply] using this

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem gs_cst_top (p : Z ⟶ Sp R₁) (z : Z) (c : R₁) :
    gs (𝟙 Z) z ⊤ (GlobalTheory.AbLaw.cst p ⊤ c) = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c) := by
  have h1 := gs_res (𝟙 Z) z (le_top : (⊤ : Z.Opens) ≤ p ⁻¹ᵁ ⊤) trivial ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c))
  have h2 := gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom c)
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_comb_pt {d : ℕ} (b : Fin d → R₁) (p : Z ⟶ Sp R₁) (q : Z ⟶ X) (V : X.Opens) (z : Z) (hz : q z ∈ V)
    (a : Fin d → Γ(X, V)) :
    gs (𝟙 Z) z (q ⁻¹ᵁ V) (∑ l, GlobalTheory.AbLaw.cst p (q ⁻¹ᵁ V) (b l) * (q.app V).hom (a l)) =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z V (a l) := by
  rw [GlobalTheory.FlatSec.gs_comb p q V z hz b a]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gs_cst_top]

theorem exists_aff (U : X.Opens) (x : X) (hx : x ∈ U) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨V, hV, hxV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  exact ⟨V, hV, hxV, hVU⟩

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem inj_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (U : X.Opens) (a : Fin d → Γ(X, U))
    (h : ∀ z : Z, q z ∈ U →
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z U (a l) = 0) :
    ∀ l, a l = 0 := by
  intro l
  apply fn_ext
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_aff U x hx
  have h0 := (aff_coeff ρ₁ b hb H hV).2 (fun l => GlobalTheory.AbLaw.rs X hVU (a l)) (fn_ext fun z hz => by
    rw [gs_comb_pt b p q V z hz, gs_zero0]
    refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) (h z (hVU hz))
    rw [gs_res q z hVU hz])
  have e := congrFun h0 l
  have e2 := gs_res (𝟙 X) x hVU hxV (a l)
  simp only [Pi.zero_apply] at e
  rw [← e2]
  erw [e]
  rw [gs_zero0, gs_zero0]

theorem surj_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (U : X.Opens) (t : Γ(Z, q ⁻¹ᵁ U)) :
    ∃ a : Fin d → Γ(X, U), ∀ z : Z, q z ∈ U →
      gs (𝟙 Z) z (q ⁻¹ᵁ U) t =
        ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z U (a l) := by
  classical
  choose V hV hxV hVU using fun x : U => exists_aff U x.1 x.2
  have hle : ∀ x, q ⁻¹ᵁ V x ≤ q ⁻¹ᵁ U := fun x z hz => hVU x hz
  choose c hc using fun x : U => (aff_coeff ρ₁ b hb H (hV x)).1 (GlobalTheory.AbLaw.rs Z (hle x) t)
  have hcg : ∀ x z, q z ∈ V x → gs (𝟙 Z) z (q ⁻¹ᵁ U) t =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (V x) (c x l) := by
    intro x z hz
    rw [← gs_res (𝟙 Z) z (hle x) hz t, ← gs_comb_pt b p q (V x) z hz]
    exact congrArg _ (hc x)
  have hcomp : ∀ l x y, GlobalTheory.AbLaw.rs X (inf_le_left : V x ⊓ V y ≤ V x) (c x l) =
      GlobalTheory.AbLaw.rs X (inf_le_right : V x ⊓ V y ≤ V y) (c y l) := by
    intro l x y
    refine sub_eq_zero.1 (inj_gen ρ₁ b hb H (V x ⊓ V y)
      (fun l => GlobalTheory.AbLaw.rs X inf_le_left (c x l) - GlobalTheory.AbLaw.rs X inf_le_right (c y l)) (fun z hz => ?_) l)
    have e : ∀ l, gs q z (V x ⊓ V y) (GlobalTheory.AbLaw.rs X inf_le_left (c x l) - GlobalTheory.AbLaw.rs X inf_le_right (c y l)) =
        gs q z (V x) (c x l) - gs q z (V y) (c y l) := fun l => by
      rw [gs_eq q z _ hz, map_sub, map_sub, ← gs_eq q z _ hz, ← gs_eq q z _ hz, gs_res q z _ hz, gs_res q z _ hz]
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    rw [← hcg x z hz.1, ← hcg y z hz.2, sub_self]
  have hcov : U ≤ iSup V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  choose s hs using fun l => X.sheaf.existsUnique_gluing' V U (fun x => homOfLE (hVU x)) hcov
    (fun x => c x l) (fun x y => hcomp l x y)
  refine ⟨s, fun z hz => ?_⟩
  rw [hcg ⟨q z, hz⟩ z (hxV ⟨q z, hz⟩)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← (hs l).1 ⟨q z, hz⟩]
  exact congrArg _ (gs_res q z (hVU ⟨q z, hz⟩) (hxV ⟨q z, hz⟩) (s l))

end GlobalTheory.FrameCoeff

namespace GlobalTheory.FrameCoeff

variable {R R₁ : Type} [CommRing R] [CommRing R₁] {X Z : Scheme.{0}}

theorem main_gen (ρ₁ : R →+* R₁) {d : ℕ} (b : Fin d → R₁)
    (hb : ∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l)
    {f : X ⟶ Sp R} {q : Z ⟶ X} {p : Z ⟶ Sp R₁} (H : IsPullback q p f (spMap ρ₁))
    (L : LB X) (W O : X.Opens) (hOW : O ≤ W)
    (τ : ∀ k : L.ι, Γ(Z, q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k)ˣ) (hτ : FrameAlong L q (q ⁻¹ᵁ W) τ) :
    ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧
      ∀ (z : Z) (k : L.ι), q z ∈ O → q z ∈ L.U k →
        gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val =
          ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (O ⊓ L.U k) (s l k) := by
  have hle : ∀ k, q ⁻¹ᵁ (O ⊓ L.U k) ≤ q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k := fun k z hz => ⟨hOW hz.1, hz.2⟩
  choose a ha using fun k => surj_gen ρ₁ b hb H (O ⊓ L.U k) (GlobalTheory.AbLaw.rs Z (hle k) (τ k).val)
  have hτg : ∀ k z, q z ∈ O ⊓ L.U k → gs (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) (τ k).val =
      ∑ l, gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs q z (O ⊓ L.U k) (a k l) := by
    intro k z hz
    rw [← gs_res (𝟙 Z) z (hle k) hz]
    exact ha k z hz
  refine ⟨fun l k => a k l, fun l => ?_, fun z k hO hk => hτg k z ⟨hO, hk⟩⟩
  intro x k k' hx hk hk'
  have hV : O ⊓ L.U k ≤ L.U k := inf_le_right
  have hW : O ⊓ L.U k' ≤ L.U k' := inf_le_right
  have h0 := inj_gen ρ₁ b hb H ((O ⊓ L.U k) ⊓ (O ⊓ L.U k'))
    (fun l => GlobalTheory.AbLaw.rs X inf_le_left (a k l) -
      GlobalTheory.AbLaw.rs X (inf_le_inf hV hW) (L.g k k').val * GlobalTheory.AbLaw.rs X inf_le_right (a k' l)) (fun z hz => ?_) l
  · have e := congrArg (gs (𝟙 X) x _) h0
    rw [GlobalTheory.FlatSec.gs_diff hV hW (a k l) (a k' l) (𝟙 X) x ⟨⟨hx, hk⟩, ⟨hx, hk'⟩⟩, gs_zero0] at e
    exact sub_eq_zero.1 e
  · have e1 : ∀ l, gs q z _ (GlobalTheory.AbLaw.rs X inf_le_left (a k l) -
        GlobalTheory.AbLaw.rs X (inf_le_inf hV hW) (L.g k k').val * GlobalTheory.AbLaw.rs X inf_le_right (a k' l)) =
        gs q z _ (a k l) - (gm q z (L.U k ⊓ L.U k') (L.g k k')).val * gs q z _ (a k' l) :=
      fun l => GlobalTheory.FlatSec.gs_diff hV hW _ _ q z hz
    simp only [e1, mul_sub, Finset.sum_sub_distrib]
    have hfr := congrArg Units.val (hτ z k k' (hOW hz.1.1) hz.1.2 hz.2.2)
    rw [Units.val_mul, ← gs_unit (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k) ⟨hOW hz.1.1, hz.1.2⟩ (τ k),
      ← gs_unit (𝟙 Z) z (q ⁻¹ᵁ W ⊓ q ⁻¹ᵁ L.U k') ⟨hOW hz.1.1, hz.2.2⟩ (τ k'),
      hτg k z hz.1, hτg k' z hz.2] at hfr
    rw [hfr, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameCoeff

theorem GlobalTheory.FrameCoeff.frame_coeff : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ (W O : X.Opens), O ≤ W → IsAffineOpen O → ∀ (τ : ∀ k : L.ι, Γ((pullback f (spMap ρ₁)), (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k)ˣ), FrameAlong L (pullback.fst f (spMap ρ₁)) ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W) τ → ∃ s : Fin d → ∀ k : L.ι, Γ(X, O ⊓ L.U k), (∀ l, IsSecOver L O (s l)) ∧ ∀ (z : (pullback f (spMap ρ₁) : Scheme.{0})) (k : L.ι), (pullback.fst f (spMap ρ₁)) z ∈ O → (pullback.fst f (spMap ρ₁)) z ∈ L.U k → gs (𝟙 (pullback f (spMap ρ₁))) z ((pullback.fst f (spMap ρ₁)) ⁻¹ᵁ W ⊓ (pullback.fst f (spMap ρ₁)) ⁻¹ᵁ L.U k) (τ k).val = ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z (O ⊓ L.U k) (s l k) := by
  intro R R₁ _ _ ρ₁ d b hb X f L hL W O hOW hO τ hτ
  exact GlobalTheory.FrameCoeff.main_gen ρ₁ b hb (IsPullback.of_hasPullback f (spMap ρ₁)) L W O hOW τ hτ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDegreeCmLogPeriod
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatCore

theorem frameDeg_of_cmDiff : CMDiffSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → FrameDeg U x (GlobalTheory.CM.logOm E χ).re := by
  intro hCM E _ _ _ H hH _ χ hχ Dw l Xo c r U x hL Z τ s ρ hρ
  obtain ⟨K, iF, iN, iA, y, ρ₀, σ₁, X, t₀, hy, hm₁, hm₂, hρ₀⟩ := GlobalTheory.T.exists_cm_goodReduction_point_on_component E H Dw l Xo c r U x hL Z
  obtain ⟨F⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K X.B.pol
  obtain ⟨⟨h, hh⟩, -⟩ :=
    GlobalTheory.CM.LieMetric.exists_unique_isHerm GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 K X.B.pol F
  let f : 𝓞 E →+* K := (algebraMap c.F K).comp (embK c τ.1)
  have hf : ∀ a, IsIntegral ℤ (f a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map f.toIntAlgHom
  let t : 𝓞 E →+* 𝓞 K := f.codRestrict (integralClosure ℤ K).toSubring hf
  have ht : ∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a) := fun a => rfl
  obtain ⟨hfin, hdeg⟩ := GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy X.B t₀ hm₁ hm₂ F h hh t ht
  have htρ : t H.rt = ρ₀ := by
    apply RingOfIntegers.ext
    rw [ht, hρ₀ τ]
  exact ⟨hfin, hdeg.trans (hCM E H hH χ hχ K ρ₀ σ₁ Dw.p Dw.q X F h hh t htρ)⟩

end GlobalTheory.FlatCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCanonicalLiftPrimitiveHodge
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ),
    (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (x : G.RigExt), IsCan t c x → G.rigToExt x = 0 → c ∈ PrimitiveSubmodule A := by
  intro p _ R _ N hN A _ hA G t c x hx h0
  have : IsCommMonObj A := hA.comm
  obtain ⟨d, z, w, hz, -, rfl⟩ := hx
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow]; exact hN

  have hmk : (Submodule.Quotient.mk z : G.VecExt) = 0 := h0
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmk
  have hcob : d.coc N = cobOne R (G.A N) (B.1 N) := by
    rw [← hz N, ← hB]; rfl

  have hchiN : chi (p ^ N) d.g (G.A N) (t.y N) = 0 := by
    rw [← Dat.diagSum_coc R A p G t c d N hN, hcob]
    exact diagSum_cobOne_eq_zero p R G N hN (B.1 N)

  have hchi : ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt A D), y ^ (p ^ N) = 1 →
      chi (p ^ N) d.g D y = 0 := by
    intro D _ _ y hy
    obtain ⟨φ, rfl⟩ := t.surj N D y hy
    have h1 : t.y N ^ (p ^ N) = 1 := t.y_pow N
    have hn := chi_natural (p ^ N) R hq A (fv d.f) d.g d.add (G.A N) D φ (t.y N)
    rw [h1, hchiN, map_zero, sub_zero, sub_self] at hn
    exact hn
  have hcoc := (fv_isCoc_and_ev_eq R A d.f).1
  have hsym := isSymCoc_of_isAdd R A hA (fv d.f) d.g d.add
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  obtain ⟨k, hk⟩ := Descent.exists_isCob (p ^ N) R hq A (fv d.f) d.g hcoc d.add hsym hchi
    (fun D _ _ y ↦ PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) hpos D y)
  have hF := (mem_hodgeFiltration_iff_pointwiseCoboundary R A d.f).2 ⟨k, hk⟩
  rw [d.cl] at hF
  exact hF

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEquivariantDeRham
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbDatum

open GlobalTheory.ConjSeq

theorem frobDR_primPull (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (c : primDR B) :
    frobDR p R hR A (primPull (dp0 R) (𝟙 _) f c) = primPull (dp0 R) (𝟙 _) f (frobDR p R hR B c) := by
  have k := (frobMor p R hR B (cast_left p R hR B)).comp (homMor (dp0 R) (𝟙 _) f)
  exact (GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) f) (frobMor p R hR A (cast_left p R hR A)) k (fun _ ↦ rfl)
    (GlobalTheory.VB.frob_naturality p _ f.left _) c).trans
    (GrpMor.pull_pull (frobMor p R hR B (cast_left p R hR B)) (homMor (dp0 R) (𝟙 _) f) k (fun _ ↦ rfl) rfl c).symm

theorem linFrob_isEquivariant : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (A : Over T) [GrpObj A] (i : OAct O A) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (p : ℕ) [Fact p.Prime] (h0 : (p : Γ(T, ⊤)) = 0) (ρ : O →+* End H) (Ψ : (frobPull p h0).obj H ⟶ H),
    IsDRAct e i ρ → IsLinFrob e p h0 Ψ → IsEquivariant (pullAct ρ (frob T p h0)) ρ Ψ := by
  intro O _ T A _ i H e p _ h0 ρ Ψ hρ hΨ x
  refine frobPull_hom_ext_affine p h0 fun V hV s ↦ (e V hV).injective ?_
  have e1 : (VB.act (pullAct ρ (frob T p h0)) x ≫ Ψ).app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s) =
      Ψ.app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) ((VB.act ρ x).app V s)) :=
    congrArg (Ψ.app V) (QCoh.pullback_map_app_pullbackSections (frob T p h0) (VB.act ρ x) (le_refl V) s)
  have e2 : (Ψ ≫ VB.act ρ x).app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s) =
      (VB.act ρ x).app V (Ψ.app V (QCoh.pullbackSections (frob T p h0) H (le_refl V) s)) := rfl
  refine (congrArg (e V hV) e1).trans (Eq.trans ?_ (congrArg (e V hV) e2).symm)
  rw [hΨ V hV, hρ x V hV, hρ x V hV, hΨ V hV]
  haveI := i.hom x
  exact frobDR_primPull p _ (A := onAff A hV) (B := onAff A hV) ((Over.pullback hV.fromSpec).map (i.act x)) _

end GlobalTheory.AbDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodge
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem frobDR_eq_zero_mem_F1prim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ c : primDR A, frobDR p k hk A c = 0 → c ∈ PrimitiveSubmodule A := by
  intro p _ k _ _ hk A _ hA c hc
  have hI : IsIntegral A.left := GlobalTheory.PrimVan.isIntegral_left hA
  have hS : Smooth (A.hom ≫ 𝟙 _) := by
    rw [Category.comp_id]; exact hA.smooth
  exact GlobalTheory.T.mem_hodgeFiltrationOne_of_frobenius_pull_eq_zero p k hk A.left (A.hom ≫ 𝟙 _) (cast_left p k hk A)
    (frobMor p k hk A (cast_left p k hk A)).isMor c.1 (congrArg Subtype.val hc)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPeriodChange
section
namespace GlobalTheory.TangentVecUnique

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

theorem eq_of_isDiff_of_isTangent : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (n : ℕ) (u : HolUnif A L n)
    (v : epsR ℂ ⟶ A) (w w' : Fin n → ℂ), IsTangent v → u.IsDiff w v → u.IsDiff w' v → w = w' := by
  intro A _ L n u v w w' hv h h'
  have hd : u.IsDiff (w - w') (toUnit (epsR ℂ) ≫ η[A]) := by
    intro U h₁ f
    have hv₁ : ⊤ ≤ v.left ⁻¹ᵁ U := (GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) hv U).2
      ((GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) (GlobalTheory.ArchMetricCompare.isTangent_zero A) U).1 h₁)
    rw [GlobalTheory.ArchMetricCompare.isDiff_zero u U h₁ f, map_zero, map_sub, ← h U hv₁ f, ← h' U hv₁ f, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.ArchMetricCompare.eq_zero_of_isDiff u hd)

end GlobalTheory.TangentVecUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GAdjSndOfIsProdUnif
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.SndAdj

open GlobalTheory.CechPic

theorem psum_comp_hom {S : Scheme.{0}} {T H H' : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    (f : H ⟶ H') [IsMonHom f] {n : ℕ} (x : Fin n → (T ⟶ H)) (I : Finset (Fin n)) :
    psum H x I ≫ f = psum H' (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (· ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem sum_cube_zero {S : Scheme.{0}} {T H : Over S} [GrpObj H] [IsCommMonObj H] {M : Type*} [AddCommGroup M]
    (F : (T ⟶ H) → M) (y : Fin 2 → (T ⟶ H)) (hy : y 0 = 1) :
    ∑ I : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - I.down.card)) • F (psum H y I.down) = 0 := by
  refine (Fintype.sum_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => ((-1 : ℤ) ^ (2 - I.card)) • F (psum H y I))
    (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide]
  simp only [ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.psum_eq_prod]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [hy]

theorem gAdj_snd_of_isProdUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have cL : cls _ hL = CechPic.pull (fst G₁ G₂).left (cls _ hL₁) + CechPic.pull (snd G₁ G₂).left (cls _ hL₂) :=
    (cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj cubeLB
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL₂ _ _)).1 ?_
  rw [cls_linComb hL, cls_linComb hL₂, cL]
  simp only [map_add, ← CechPic.pull_comp, smul_add, Finset.sum_add_distrib]
  have h₁ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (fst G₁ G₂).left = (psum G₁ ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  have h₂ : ∀ J : Finset (Fin 2), (psum (G₁ ⊗ G₂) ![fst G₂ (G₁ ⊗ G₂) ≫ lift 1 (𝟙 G₂), snd G₂ (G₁ ⊗ G₂)] J).left ≫
      (snd G₁ G₂).left = (psum G₂ ![fst G₂ (G₁ ⊗ G₂), snd G₂ (G₁ ⊗ G₂) ≫ snd G₁ G₂] J).left := fun J => by
    rw [← Over.comp_left, psum_comp_hom]
    congr 2
    funext i
    fin_cases i <;> simp
  simp only [h₁, h₂]
  exact add_eq_right.2 (sum_cube_zero
    (fun u : G₂ ⊗ G₁ ⊗ G₂ ⟶ G₁ => CechPic.pull u.left (cls _ hL₁)) ![1, snd G₂ (G₁ ⊗ G₂) ≫ fst G₁ G₂] rfl)

end GlobalTheory.MumProd.SndAdj
end
end

