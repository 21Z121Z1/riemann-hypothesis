import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem closed1_eq_top_of_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Closed1 (OAff A.hom) = ⊤ := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  have hP := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hg
  rw [eq_top_iff]
  intro w _
  obtain ⟨n, u, v, hw⟩ := GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge R _ (OAff A.hom) hF h0 w
  have hμ : ClRel (OAff (A ⊗ A).hom) (pF μ[A] w) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (μ[A]).left (ovw μ[A]) w n u v hw
  have h1 : ClRel (OAff (A ⊗ A).hom) (pF (fst A A) w) (fun k ↦ pF (fst A A) (u k))
      (fun k ↦ pF (fst A A) (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (fst A A).left (ovw (fst A A)) w n u v hw
  have h2 : ClRel (OAff (A ⊗ A).hom) (pF (snd A A) w) (fun k ↦ pF (snd A A) (u k))
      (fun k ↦ pF (snd A A) (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (snd A A).left (ovw (snd A A)) w n u v hw
  have hsum : wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) =
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) +
        wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) := by
    funext T
    have e := hP w
    calc _ = dOne R _ ((pF μ[A] w).1 T) := (hμ T).symm
      _ = dOne R _ ((pF (fst A A) w).1 T + (pF (snd A A) w).1 T) :=
          congrArg (fun x : GlobForm (A ⊗ A).hom ↦ dOne R _ (x.1 T)) e
      _ = dOne R _ ((pF (fst A A) w).1 T) + dOne R _ ((pF (snd A A) w).1 T) := map_add _ _ _
      _ = _ := congrArg₂ (· + ·) (h1 T) (h2 T)
  have hz := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hg n u v hsum
  exact fun T ↦ (hw T).trans (congrFun hz T)

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyCechVanishingAboveDegreeStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_cech_vanishing_above_degree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ c : ℕ, ∀ P : LB A.left, P.IsLB → ∀ j : ℕ, c ≤ j → ¬ NV A P j := by
  first | exact @GlobalTheory.AmpleGen.not_NV_of_ge | exact GlobalTheory.AmpleGen.not_NV_of_ge | (intros; apply GlobalTheory.AmpleGen.not_NV_of_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySquareLinearEndomorphismFiniteLoca
section
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

theorem zpow_two_var {G : Type*} [CommGroup G] (x y : G) (a b c d a' b' : ℤ) :
    (x ^ a * y ^ b) ^ a' * (x ^ c * y ^ d) ^ b' = x ^ (a * a' + c * b') * y ^ (b * a' + d * b') := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  exact _root_.mul_mul_mul_comm _ _ _ _

theorem comp_zpow_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {G X Y : C} [GrpObj G]
    (f : X ⟶ Y) (g : Y ⟶ G) (n : ℤ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast, comp_pow]
  | negSucc n => simp only [zpow_negSucc, GrpObj.comp_inv, comp_pow]

theorem psiMap_comp {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (a b c d a' b' c' d' : ℤ) :
    psiMap A a b c d ≫ psiMap A a' b' c' d' =
      psiMap A (a * a' + c * b') (b * a' + d * b') (a * c' + c * d') (b * c' + d * d') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, psiMap_fst, psiMap_fst, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst,
      psiMap_snd, zpow_two_var]
  · rw [Category.assoc, psiMap_snd, psiMap_snd, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst,
      psiMap_snd, zpow_two_var]

theorem psiMap_diag {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (n : ℕ) :
    psiMap A n 0 0 n = Out.mulA (A ⊗ A) n := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [psiMap_fst, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.mul_one, zpow_natCast]
  · rw [psiMap_snd, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.one_mul, zpow_natCast]

theorem finite_etale_of_comp_eq {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] (f g m : X ⟶ X) [IsFinite m] [Etale m] (hg : g ≫ p = p)
    (h1 : f ≫ g = m) (h2 : g ≫ f = m) : IsFinite f ∧ Etale f := by
  have hgs : IsSeparated g :=
    MorphismProperty.of_postcomp (W' := ⊤) @IsSeparated g p trivial (by rw [hg]; infer_instance)
  haveI : LocallyOfFiniteType (g ≫ p) := by rw [hg]; infer_instance
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g p
  haveI : FormallyUnramified (g ≫ f) := by rw [h2]; infer_instance
  haveI : FormallyUnramified g := FormallyUnramified.of_comp g f
  haveI : Etale (f ≫ g) := by rw [h1]; infer_instance
  haveI : IsFinite (f ≫ g) := by rw [h1]; infer_instance
  exact ⟨MorphismProperty.of_postcomp @IsFinite (W' := @IsSeparated) f g hgs inferInstance,
    Etale.of_comp f g⟩

theorem exists_sign_mul (d : ℤ) : ∃ s : ℤ, s * d = (d.natAbs : ℤ) := by
  rcases Int.natAbs_eq d with h | h
  · exact ⟨1, by rw [_root_.one_mul]; exact h⟩
  · exact ⟨-1, by rw [h]; ring_nf; simp⟩

theorem psiMap_finite_locallyFree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K))
    [GrpObj A], IsAbelianScheme A → ∀ a₁ b₁ a₂ b₂ : ℤ, ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0 →
    IsFinite (psiMap A a₁ b₁ a₂ b₂).left ∧ Flat (psiMap A a₁ b₁ a₂ b₂).left ∧
      LocallyOfFinitePresentation (psiMap A a₁ b₁ a₂ b₂).left ∧
      ∃ r : ℕ, (∀ y, (psiMap A a₁ b₁ a₂ b₂).left.finrank y = r) ∧ (r : K) ≠ 0 := by
  intro K _ _ A _ hA a₁ b₁ a₂ b₂ hd
  haveI := hA.comm
  set n := (a₁ * b₂ - b₁ * a₂).natAbs with hn_def
  have hn : (n : K) ≠ 0 := by
    rcases Int.natAbs_eq (a₁ * b₂ - b₁ * a₂) with h | h
    · rw [h, Int.cast_natCast] at hd; exact hd
    · rw [h, Int.cast_neg, Int.cast_natCast, neg_ne_zero] at hd; exact hd
  haveI hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨hfin, -, het, r, hr0, -, hall, -⟩ :=
    GlobalTheory.AbelianMulFin.mulA_finite_locallyFree K (A ⊗ A) n hn
  obtain ⟨s, hs⟩ := exists_sign_mul (a₁ * b₂ - b₁ * a₂)
  rw [← hn_def] at hs
  set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ
  set ψ' := psiMap A (s * b₂) (-(s * b₁)) (-(s * a₂)) (s * a₁) with hψ'
  have h1 : ψ ≫ ψ' = Out.mulA (A ⊗ A) n := by
    rw [hψ, hψ', psiMap_comp, ← psiMap_diag]
    congr 1 <;> push_cast <;> first | ring1 | linear_combination hs
  have h2 : ψ' ≫ ψ = Out.mulA (A ⊗ A) n := by
    rw [hψ, hψ', psiMap_comp, ← psiMap_diag]
    congr 1 <;> push_cast <;> first | ring1 | linear_combination hs
  have h1' : ψ.left ≫ ψ'.left = (Out.mulA (A ⊗ A) n).left := by rw [← Over.comp_left, h1]
  have h2' : ψ'.left ≫ ψ.left = (Out.mulA (A ⊗ A) n).left := by rw [← Over.comp_left, h2]
  haveI := hAA.proper
  haveI := hAA.smooth
  haveI := hAA.geomConnected
  obtain ⟨hψfin, hψet⟩ := finite_etale_of_comp_eq (A ⊗ A).hom ψ.left ψ'.left _ (Over.w ψ') h1' h2'
  obtain ⟨hψ'fin, hψ'et⟩ := finite_etale_of_comp_eq (A ⊗ A).hom ψ'.left ψ.left _ (Over.w ψ) h2' h1'
  haveI : ConnectedSpace (A ⊗ A).left :=
    GeometricallyConnected.connectedSpace (A ⊗ A).hom (A ⊗ A).hom.isOpenMap
  let o : (A ⊗ A).left := Classical.arbitrary _
  set r' := ψ.left.finrank o with hr'
  have hall' : ∀ y, ψ.left.finrank y = r' := fun y =>
    (Scheme.Hom.isLocallyConstant_finrank ψ.left).apply_eq_of_preconnectedSpace y o
  refine ⟨hψfin, inferInstance, inferInstance, r', hall', fun h0 => hr0 ?_⟩
  have e := GlobalTheory.FinrankComp.finrank_comp_of_const ψ.left ψ'.left r' hall' o
  rw [h1', hall o] at e
  rw [e, Nat.cast_mul, h0, zero_mul]

end GlobalTheory.AmpleGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsOriginBoxValueExponentLeStatement
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_originBoxValueExponent_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k), 1 ≤ G.s → ∀ (a a' : ℤ) (N : ℕ), (∀ i j, i ≤ G.m → j ≤ G.m → G.rank (i, j) ≤ N) → |expo G a a'| ≤ 8 * ((G.m : ℤ) ^ 3 * (N : ℤ) ^ 2 * (|a| + |a'|)) := by
  first | exact @GlobalTheory.OriginBox.abs_expo_le | exact GlobalTheory.OriginBox.abs_expo_le | (intros; apply GlobalTheory.OriginBox.abs_expo_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
section
noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def act {R κ : Type} [CommRing R] [Fintype κ] (a : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_mul {R κ : Type} [CommRing R] [Fintype κ] (a b : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) :
    act (a * b) w = act a (act b w) := by
  simp only [act, Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]

theorem act_fromBlocks {R κ : Type} [CommRing R] [Fintype κ] (A B C D : Matrix κ κ R) (w : (κ → R) × (κ → R)) :
    act (Matrix.fromBlocks A B C D) w = (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2) := by
  simp only [act, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

variable {F : Type} [Field F] [NumberField F]

def ind (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def IsFam {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (κ → Fv F v)) ∧ ∀ᶠ v in cofinite, φ v = ind κ v

def IsOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (c : ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) : Prop :=
  c ≠ 0 ∧ Function.Surjective ei ∧
  (∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _)) ∧
  (∀ v (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) =
    schr (GlobalTheory.LatVac.psiAt ψ v) (act (a.map (algebraMap F (Fv F v))) w) (ev v φ)) ∧
  (∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v) ∧
  ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
    e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v => ev v (φ v)) ∧
    (∀ w : (κ → AF F) × (κ → AF F), e (schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      schr ψ (act (a.map (algebraMap F (AF F))) w) (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) ∧
    thetaSum F (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = c * thetaSum F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)

def HasOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ e c ei ev, IsOp ψ a e c ei ev

theorem IsOp.isFam {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e c ei ev}
    (h : IsOp ψ a e c ei ev) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : IsFam fun v => ev v (φ v) := by
  obtain ⟨-, -, hbij, -, hind, -⟩ := h
  refine ⟨fun v => (hbij v).mapsTo (hφ.1 v), ?_⟩
  filter_upwards [hφ.2, hind] with v h1 h2
  rw [h1, h2]

theorem HasOp.mul {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a b : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (ha : HasOp ψ a) (hb : HasOp ψ b) : HasOp ψ (a * b) := by
  obtain ⟨e₁, c₁, ei₁, ev₁, h₁⟩ := ha
  obtain ⟨e₂, c₂, ei₂, ev₂, h₂⟩ := hb
  have h₂' := h₂
  obtain ⟨hc₁, hs₁, hb₁, hw₁, hi₁, hp₁⟩ := h₁
  obtain ⟨hc₂, hs₂, hb₂, hw₂, hi₂, hp₂⟩ := h₂
  refine ⟨e₁ ∘ₗ e₂, c₁ * c₂, ei₁.comp ei₂, fun v => ev₁ v ∘ₗ ev₂ v, mul_ne_zero hc₁ hc₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs₁.comp hs₂
  · intro v
    exact (hb₁ v).comp (hb₂ v)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hw₂ v w φ hφ, hw₁ v _ _ ((hb₂ v).mapsTo hφ), Matrix.map_mul, act_mul]
  · filter_upwards [hi₁, hi₂] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ
    have hφ' : IsFam fun v => ev₂ v (φ v) := IsOp.isFam h₂' hφ
    obtain ⟨hq₂, hw₂', ht₂⟩ := hp₂ f φ hφ
    obtain ⟨hq₁, hw₁', ht₁⟩ := hp₁ (ei₂ f) (fun v => ev₂ v (φ v)) hφ'
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, hq₂, hq₁]
    · intro w
      simp only [LinearMap.comp_apply]
      rw [hw₂' w, hq₂, hw₁' _, Matrix.map_mul, act_mul]
    · simp only [LinearMap.comp_apply]
      rw [hq₂, ht₁, ← hq₂, ht₂, mul_assoc]

theorem hasOp_one {κ : Type} [Fintype κ] [DecidableEq κ] (ψ : AddChar (AF F) ℂ) : HasOp ψ (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) := by
  have h1 : ∀ {R : Type} [CommRing R] (w : (κ → R) × (κ → R)), act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) w = w := by
    intro R _ w
    simp only [act, Matrix.one_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
  refine ⟨LinearMap.id, 1, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, one_ne_zero,
    Function.surjective_id, fun v => Set.bijOn_id _, ?_, ?_, ?_⟩
  · intro v w φ _
    simp only [LinearMap.id_apply, Matrix.map_one _ (map_zero _) (map_one _), h1]
  · exact Filter.Eventually.of_forall fun v => rfl
  · intro f φ _
    refine ⟨rfl, fun w => ?_, by simp⟩
    simp only [LinearMap.id_apply, Matrix.map_one _ (map_zero _) (map_one _), h1]

end GlobalTheory.RatWeilOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCompletion_comap_rational_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (A : GL (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (w : Fin n → GlobalTheory.AdLat.RA F E),
    GlobalTheory.UnRep.fm F A.1 *ᵥ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      w ∈ GlobalTheory.AdLat.hat F ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  first | exact @GlobalTheory.HatPullback.main | exact GlobalTheory.HatPullback.main | (intros; apply GlobalTheory.HatPullback.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchrodinger_tensor_eq_local_of_supportedAt : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  first | exact @GlobalTheory.SchrLoc.schr_tens_of_at | exact GlobalTheory.SchrLoc.schr_tens_of_at | (intros; apply GlobalTheory.SchrLoc.schr_tens_of_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableKernelRouteBigVertex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.BigRoute

theorem theta_of_matched_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (_ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (_ : d ∈ Θ.support),
    IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ d hd
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have v2 := ρ.vT_is t (i + 1) j i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem continuous_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (_ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ g₁
  have hc := W.om_is (.chi (i : ℕ) (j + 1)) ⟨i.2, j.2⟩
  have hm := W.om_is (.mu t ((i : ℕ) + 1) j) ⟨i.2, j.2⟩
  have hK : ∀ d ∈ Θ.support, Continuous (fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      W.kerA (.right i (j + 1)) d.1.2 q.1 q.2 * W.kerA (.down t (i + 1) j) d.2 q.2 g₁) := by
    intro d hd
    obtain ⟨h1, h2⟩ := theta_of_matched_big hΘ hd
    refine Continuous.mul ?_ ?_
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.chi (i : ℕ) (j + 1))) (negGA _ q.2) q.1 d.1.2
      exact (hc.om_cont _ h1 0).comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.mu t ((i : ℕ) + 1) j)) g₁ q.2 d.2
      exact (hm.om_cont _ h2 0).comp (continuous_const.prodMk continuous_snd)
  unfold kerBig
  simp only [Finsupp.sum]
  exact continuous_finset_sum _ fun d hd => continuous_const.mul (hK d hd)

theorem aestronglyMeasurable_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁
  exact (continuous_kerBig W B ρ t i j Θ Θ' hΘ g₁).aestronglyMeasurable

end GlobalTheory.BigRoute
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_div_beta_ramified_at_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.E)), P ∈ L.Q t →
      P.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.TwistRam.not_unrAt_alpha_div_beta | exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta | (intros; apply GlobalTheory.TwistRam.not_unrAt_alpha_div_beta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_div_beta_ramified_first : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∈ S1 D →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ | exact GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ | (intros; apply GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutsideStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_unramified_outside : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) → GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j) w := by
  first | exact @GlobalTheory.FunObj.alpha_unrAt | exact GlobalTheory.FunObj.alpha_unrAt | (intros; apply GlobalTheory.FunObj.alpha_unrAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticCompatibilityStandardKernelDataTrueColum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ColRows.analyticTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.AnalyticTie (I.rec7 l Z) t.δ t.χ t.cD ∧ t.tup (I.rec7 l Z).what₂.mu0 = 1 ∧ t.m2 = (I.rec7 l Z).R.m - 2 := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t hJ hS
  obtain ⟨-, -, hDg, -⟩ := GlobalTheory.Core.Ht2.analyticTies_trueCols I hOk (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1 l Z hJ

  have hcD : t.cD = I.J.cD := (t.O_dgen B.u₀ I.mu0).symm.trans (hS.O.dgen B.u₀ I.mu0)
  refine ⟨⟨t.cc_rec ▸ t.δ_ok, t.χ_ok, hcD ▸ hDg⟩, ?_, hS.m2⟩

  obtain ⟨hX, -, -, -, -, hSS, -, htup, -⟩ := hS
  cases t
  subst hX
  subst hSS
  cases htup
  exact I.trueColumn_tuple_trivial_eq_one
end

