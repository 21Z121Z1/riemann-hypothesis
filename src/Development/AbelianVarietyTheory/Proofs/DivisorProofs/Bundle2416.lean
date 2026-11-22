import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFst
section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def IsProjMat {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (σ : 𝓞 E →+* R) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Matrix (Fin g) (Fin g) R) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S),
    EigRowsAt t (spMap φ ≫ ξ) (φ.comp σ) (bcV t φ e) (U.map φ) ∧
    ∀ w v, IsCombAtG t (spMap φ ≫ ξ) (bcV t φ e) w v → IsEigG t (φ.comp σ) v →
      Matrix.vecMul w (U.map φ) = ((discr E : ℤ) : S) • w

open GlobalTheory.FlatModel.Proj in

theorem exists_isProjMat {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t ξ e) (σ : 𝓞 E →+* R) :
    ∃ U : Matrix (Fin g) (Fin g) R, IsProjMat t ξ σ e U := by
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_dual b (discr_ne_zero E)
  have hbas : ∀ w, IsTanAtG t ξ w → ∃ a, IsCombAtG t ξ e a w := fun w hw => by
    have h0 : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
      have : dualMap (RingHom.id R) = RingHom.id _ := by ext s <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have := he.2 R (RingHom.id R) w (by rwa [h0, Category.id_comp])
    simp only [h0, h1, Category.id_comp] at this
    exact this.exists
  choose ρ hρ using fun (a : 𝓞 E) (k : Fin g) =>
    hbas _ (GlobalTheory.LieMet.isTan_tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k))))
  refine ⟨Matrix.of fun k j => ∑ i, σ (c i) * ρ (b i) k j, fun S _ φ => ?_⟩
  have he' := isTanBasis_bc he φ
  let T : Fin g → TanM (spMap φ ≫ ξ) t.G := fun j => GlobalTheory.LieMet.tanOf (he'.1 j)
  have hT : bcV t φ e = fun j => (tv (T j)).left := rfl
  have hA : ∀ a k, actR t.act a (T k) = ∑ j, φ (ρ a k j) • T j := fun a k => by
    refine (GlobalTheory.LieMet.isComb_iff T _ _).1 ?_
    have := GlobalTheory.GradedPieces.comb_map φ rfl (hρ a k)
    have e1 : spMap (dualMap φ) ≫ (tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k)))).left =
        (tv (actR t.act a (T k))).left := (Category.assoc _ _ _).symm
    rw [e1] at this
    exact this
  have hU : ∀ k, ∑ j, φ (∑ i, σ (c i) * ρ (b i) k j) • T j = ∑ i, (φ.comp σ) (c i) • actR t.act (b i) (T k) := fun k => by
    simp only [hA, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul, RingHom.comp_apply]
    exact Finset.sum_comm
  refine ⟨fun k u hu a => ?_, fun w v hw hv => ?_⟩
  · rw [hT] at hu
    rw [eq_of_comb T hu, GlobalTheory.ShFam.Pad.Pull.eig_iff]
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [hU]
    exact eig_proj _ _ b c hc1 a _
  · rw [hT] at hw
    have hv0 := eq_of_comb T hw
    have hv1 : ∀ a, actR t.act a (∑ i, w i • T i) = (φ.comp σ) a • ∑ i, w i • T i := fun a => by
      rw [← GlobalTheory.ShFam.Pad.Pull.eig_iff, ← hv0]
      exact hv a
    have h2 := proj_eig _ _ b c hc2 _ hv1
    have h3 : ∑ j, (∑ k, w k • fun j => φ (∑ i, σ (c i) * ρ (b i) k j)) j • T j =
        ∑ j, (((discr E : ℤ) : S) • w) j • T j := by
      have h4 : ∑ j, (((discr E : ℤ) : S) • w) j • T j = ((discr E : ℤ) : S) • ∑ j, w j • T j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      rw [h4]
      refine Eq.trans ?_ h2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hU]
      simp only [map_sum, map_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have hu := he.2 S φ _ (GlobalTheory.LieMet.isTan_tv (∑ j, (((discr E : ℤ) : S) • w) j • T j))
    have h5 := hu.unique ((GlobalTheory.LieMet.isComb_iff T _ _).2 rfl) ((GlobalTheory.LieMet.isComb_iff T _ _).2 h3.symm)
    rw [h5]
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsFrameCoord (Y : Model Xo c β) {R : Type} [CommRing R] (ξ : Sp R ⟶ Y.X) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)) (U : Matrix (Fin g) (Fin g) R) {k : Type} [CommRing k]
    [Algebra c.F k] (φ : R →+* k) (y : FrPt Xo c k) (σ : E →+* ℂ) (M : Matrix (Fin (Dw.mult σ)) (Fin g) k)
    (C : Matrix (Fin g) (Fin (Dw.mult σ)) k) : Prop :=
  (∀ i, ∃ w : Sp (DualNumber k) ⟶ Y.oF.t.G.left,
    w ≫ Y.oF.t.G.hom = spMap (algebraMap k (DualNumber k)) ≫ GlobalTheory.AllWt.ptF y ∧ w ≫ Y.m0.toSABMap.φ = y.u σ i ∧
      IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (M i) (w ≫ Y.m.φ)) ∧
  C * M = U.map φ ∧ M * C = ((discr E : ℤ) : k) • (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) k)

def DetLaw (Z : Comp Xo c) (f : Rul Xo c) (σ₁ σ₂ : E →+* ℂ) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
  ∀ (k : Type) [Field k] [Algebra c.F k] (z y : FrPt Xo c k), LiesOn Z y → z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult σ₁)) (Fin (Dw.mult σ₁)) k) (g₂ : Matrix (Fin (Dw.mult σ₂)) (Fin (Dw.mult σ₂)) k),
      (∀ i, IsCombAt y.x (y.u σ₁) (g₁ i) (z.u σ₁ i)) → (∀ i, IsCombAt y.x (y.u σ₂) (g₂ i) (z.u σ₂ i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  infer_instance

theorem isPreimmersion_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsPreimmersion Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  unfold Model.j
  infer_instance

end GlobalTheory.FlatDenom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.FiniteOverProj

theorem isProjOver_of_isFinite_over :
    ∀ (A o : Type) [CommRing A] [CommRing o] (κ : A →+* o) (M Z : Scheme.{0}) (z : Z ⟶ Sp A) (π : M ⟶ Z) (s : M ⟶ Sp o), IsProjOver z → IsFinite π → IsNoetherianRing A → s ≫ spMap κ = π ≫ z → IsProjOver s := by
  intro A o _ _ κ M Z z π s hz hπ _ hs
  have h : IsProjOver (π ≫ z) := GlobalTheory.isProjOver_comp_of_isFinite π hz
  rw [← hs] at h
  exact GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap κ h

end GlobalTheory.FiniteOverProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FiniteCoverProper

theorem isProper_of_lift_through_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  intro R _ _ X Y₀ Y τ s t i hτ hs hi hd ht h
  have hX : IsLocallyNoetherian X := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : LocallyOfFiniteType τ := by rw [← e]; infer_instance
    have : IsLocallyNoetherian (Sp R) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
    exact LocallyOfFiniteType.isLocallyNoetherian τ
  have hsep : IsSeparated τ := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : IsImmersion j := hj
    rw [← e]; infer_instance
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hq : IsQProjOver (t ≫ τ) := ht ▸ GlobalTheory.isQProjOver_comp_of_isFinite_general s hτ
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R Y X t τ hsep hq ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have hgen : genericPoints Y ⊆ Set.range i := GlobalTheory.genericPoints_subset_range_of_isDominant i
  have hr : Set.range x ⊆ Set.range i := hx.trans hgen
  have hx₀ : IsOpenImmersion.lift i x hr ≫ i = x := IsOpenImmersion.lift_fac i x hr
  obtain ⟨z, hz⟩ := h V K y (IsOpenImmersion.lift i x hr) (by rw [← Category.assoc, hx₀, hxy])
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z := by
    rw [← hx₀, Category.assoc]; exact hz.symm
  obtain ⟨⟨x', hx', -⟩⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z, commSq := ⟨hw⟩ }).exists_lift
  exact ⟨x', hx'⟩

end GlobalTheory.FiniteCoverProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj

theorem IsPullBy.trans {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' S'' : Scheme.{0}} {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {ψ : X''.A.left ⟶ X'.A.left}
    (h' : X''.IsPullBy X' b' ψ) (h : X'.IsPullBy X b φ) : X''.IsPullBy X (b' ≫ b) (ψ ≫ φ) where
  grp := by
    refine ⟨h'.grp.1.paste_horiz h.grp.1, fun T x y x₀ y₀ hx hy ↦ ?_⟩
    let T' : Over S' := Over.mk (T.hom ≫ b')
    have wx : (x.left ≫ ψ) ≫ X'.A.hom = T'.hom := by
      rw [Category.assoc, h'.grp.1.w, ← Category.assoc, Over.w x]; rfl
    have wy : (y.left ≫ ψ) ≫ X'.A.hom = T'.hom := by
      rw [Category.assoc, h'.grp.1.w, ← Category.assoc, Over.w y]; rfl
    let x' : T' ⟶ X'.A := Over.homMk (x.left ≫ ψ) wx
    let y' : T' ⟶ X'.A := Over.homMk (y.left ≫ ψ) wy
    have e₁ : (x' * y').left = (x * y).left ≫ ψ := h'.grp.2 T x y x' y' rfl rfl
    let j : Over.mk (T'.hom ≫ b) ⟶ Over.mk (T.hom ≫ b' ≫ b) := Over.homMk (𝟙 T.left) (by simp [T'])
    have e₂ : ((j ≫ x₀) * (j ≫ y₀)).left = (x' * y').left ≫ φ :=
      h.grp.2 T' x' y' (j ≫ x₀) (j ≫ y₀)
        (by change 𝟙 T.left ≫ x₀.left = (x.left ≫ ψ) ≫ φ; rw [Category.id_comp, hx, Category.assoc])
        (by change 𝟙 T.left ≫ y₀.left = (y.left ≫ ψ) ≫ φ; rw [Category.id_comp, hy, Category.assoc])
    rw [← MonObj.comp_mul] at e₂
    change 𝟙 T.left ≫ (x₀ * y₀).left = (x' * y').left ≫ φ at e₂
    rw [Category.id_comp, e₁, Category.assoc] at e₂
    exact e₂
  act a := by
    rw [← Category.assoc, h'.act a, Category.assoc, h.act a, Category.assoc]
  pol := by
    obtain ⟨φ₂, ⟨s₁, s₂⟩, hφ⟩ := h.pol
    obtain ⟨ψ₂, ⟨t₁, t₂⟩, hψ⟩ := h'.pol
    refine ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, fun c ↦ ?_⟩
    · rw [Category.assoc, s₁, ← Category.assoc, t₁, Category.assoc]
    · rw [Category.assoc, s₂, ← Category.assoc, t₂, Category.assoc]
    · have e₁ := (GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB (X'.isLB c) ψ₂)).2 (hψ c)
      have e₂ := (GlobalTheory.CechPic.cls_eq_iff (X'.isLB c) (pull_isLB (X.isLB c) φ₂)).2 (hφ c)
      refine (GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB (X.isLB c) (ψ₂ ≫ φ₂))).1 (e₁.trans ?_)
      rw [GlobalTheory.CechPic.cls_pull (X'.isLB c), e₂, GlobalTheory.CechPic.cls_pull (X.isLB c) φ₂,
        GlobalTheory.CechPic.cls_pull (X.isLB c) (ψ₂ ≫ φ₂), GlobalTheory.CechPic.pull_comp]

end GlobalTheory.RealMult.Obj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByFactorThrough
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj

theorem IsPullBy.exists_of_comp {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' S'' : Scheme.{0}}
    {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left}
    (h : X''.IsPullBy X (b' ≫ b) χ) (h' : X'.IsPullBy X b φ) :
    ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ := by
  have hp := h'.grp.1
  let ψ : X''.A.left ⟶ X'.A.left := hp.lift χ (X''.A.hom ≫ b') (by rw [h.grp.1.w, Category.assoc])
  have hψ : ψ ≫ φ = χ := hp.lift_fst _ _ _
  have hw : ψ ≫ X'.A.hom = X''.A.hom ≫ b' := hp.lift_snd _ _ _
  refine ⟨ψ, ⟨IsGrpPullback.cancel h'.grp (by rw [hψ]; exact h.grp) hw, fun a ↦ ?_, ?_⟩, hψ⟩
  · apply hp.hom_ext
    · rw [Category.assoc, hψ, h.act, Category.assoc, h'.act, ← Category.assoc, hψ]
    · have e₁ : (X''.rm.act a).left ≫ X''.A.hom = X''.A.hom := Over.w (X''.rm.act a)
      have e₂ : (X'.rm.act a).left ≫ X'.A.hom = X'.A.hom := Over.w (X'.rm.act a)
      rw [Category.assoc, hw, ← Category.assoc, e₁, Category.assoc, e₂, hw]
  · obtain ⟨φ₂'', hsq'', hP''⟩ := h.pol
    obtain ⟨φ₂', hsq', hP'⟩ := h'.pol
    let ψ₂ : (G2 X''.A).left ⟶ (G2 X'.A).left :=
      (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A))).left
    have hsq : IsSquare ψ ψ₂ := by
      constructor
      · change (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A)) ≫ fst X'.A X'.A).left = _
        rw [lift_fst]; rfl
      · change (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A)) ≫ snd X'.A X'.A).left = _
        rw [lift_snd]; rfl
    have hcomp : ψ₂ ≫ φ₂' = φ₂'' := by
      apply pullback.hom_ext
      · change ψ₂ ≫ φ₂' ≫ (fst X.A X.A).left = φ₂'' ≫ (fst X.A X.A).left
        rw [hsq'.1, ← Category.assoc, hsq.1, Category.assoc, hψ, hsq''.1]
      · change ψ₂ ≫ φ₂' ≫ (snd X.A X.A).left = φ₂'' ≫ (snd X.A X.A).left
        rw [hsq'.2, ← Category.assoc, hsq.2, Category.assoc, hψ, hsq''.2]
    refine ⟨ψ₂, hsq, fun c ↦ ?_⟩
    have hX := X.isLB c
    have hX' := X'.isLB c
    refine (GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB hX' ψ₂)).1 ?_
    rw [(GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB hX φ₂'')).2 (hP'' c),
      GlobalTheory.CechPic.cls_pull hX' ψ₂, GlobalTheory.CechPic.cls_pull hX φ₂'', ← hcomp, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hX φ₂' (pull_isLB hX φ₂'),
      ← (GlobalTheory.CechPic.cls_eq_iff hX' (pull_isLB hX φ₂')).2 (hP' c)]

end GlobalTheory.RealMult.Obj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackCoprodDescOfPiecesOverCoprod
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isPullback_coprod_desc_of_pieces : ∀ {S S₁ S₂ T T₁ T₂ : Scheme.{0}} (u₁ : S₁ ⟶ S) (u₂ : S₂ ⟶ S), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk u₁ u₂)) → ∀ (v₁ : T₁ ⟶ T) (v₂ : T₂ ⟶ T), Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk v₁ v₂)) → ∀ (f : T ⟶ S) (f₁ : T₁ ⟶ S₁) (f₂ : T₂ ⟶ S₂), IsPullback v₁ f₁ f u₁ → IsPullback v₂ f₂ f u₂ → ∀ {X₁ X₂ Y Y₁ Y₂ : Scheme.{0}} (x₁ : X₁ ⟶ S₁) (x₂ : X₂ ⟶ S₂) (y : Y ⟶ T) (y₁ : Y₁ ⟶ T₁) (y₂ : Y₂ ⟶ T₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₁ ⟶ X₁) (i₂ : Y₂ ⟶ X₂), IsPullback j₁ y₁ y v₁ → IsPullback j₂ y₂ y v₂ → IsPullback i₁ y₁ x₁ f₁ → IsPullback i₂ y₂ x₂ f₂ → ∃ i : Y ⟶ X₁ ⨿ X₂, j₁ ≫ i = i₁ ≫ Limits.coprod.inl ∧ j₂ ≫ i = i₂ ≫ Limits.coprod.inr ∧ IsPullback i y (Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)) f := by
  intro S S₁ S₂ T T₁ T₂ u₁ u₂ hS v₁ v₂ hT f f₁ f₂ hf₁ hf₂ X₁ X₂ Y Y₁ Y₂ x₁ x₂ y y₁ y₂ j₁ j₂ i₁ i₂
    hj₁ hj₂ hi₁ hi₂
  obtain ⟨hS⟩ := hS
  obtain ⟨hT⟩ := hT
  obtain ⟨hY⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk j₁ j₂) y₁ y₂ y hj₁.w.symm hj₂.w.symm).mpr ⟨hj₁, hj₂⟩
  let x : X₁ ⨿ X₂ ⟶ S := Limits.coprod.desc (x₁ ≫ u₁) (x₂ ≫ u₂)
  obtain ⟨hX₁, hX₂⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hS) (Limits.BinaryCofan.mk (Limits.coprod.inl : X₁ ⟶ X₁ ⨿ X₂)
    Limits.coprod.inr) x₁ x₂ x (Limits.coprod.inl_desc _ _).symm (Limits.coprod.inr_desc _ _).symm).mp ⟨Limits.coprodIsCoprod X₁ X₂⟩
  obtain ⟨i, hi₁', hi₂'⟩ := Limits.BinaryCofan.IsColimit.desc' hY
    (i₁ ≫ Limits.coprod.inl) (i₂ ≫ Limits.coprod.inr)
  have e₁ : j₁ ≫ i = i₁ ≫ Limits.coprod.inl := hi₁'
  have e₂ : j₂ ≫ i = i₂ ≫ Limits.coprod.inr := hi₂'
  refine ⟨i, e₁, e₂, ?_⟩
  have H₁ : IsPullback (j₁ ≫ i) y₁ x (v₁ ≫ f) := by
    rw [e₁, hf₁.w]; exact hi₁.paste_horiz hX₁
  have H₂ : IsPullback (j₂ ≫ i) y₂ x (v₂ ≫ f) := by
    rw [e₂, hf₂.w]; exact hi₂.paste_horiz hX₂
  have w : i ≫ x = y ≫ f := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · change j₁ ≫ i ≫ x = j₁ ≫ y ≫ f
      rw [← Category.assoc j₁ i x, H₁.w, ← Category.assoc j₁ y f, hj₁.w, Category.assoc]
    · change j₂ ≫ i ≫ x = j₂ ≫ y ≫ f
      rw [← Category.assoc j₂ i x, H₂.w, ← Category.assoc j₂ y f, hj₂.w, Category.assoc]
  let c : Y ⟶ Limits.pullback x f := Limits.pullback.lift i y w
  have hcf : c ≫ Limits.pullback.fst x f = i := Limits.pullback.lift_fst _ _ _
  have hcs : c ≫ Limits.pullback.snd x f = y := Limits.pullback.lift_snd _ _ _
  have Q₁ : IsPullback (j₁ ≫ c) y₁ (Limits.pullback.snd x f) v₁ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₁)
      (by rw [Category.assoc, hcs]; exact hj₁.w)
      (IsPullback.of_hasPullback x f)
  have Q₂ : IsPullback (j₂ ≫ c) y₂ (Limits.pullback.snd x f) v₂ :=
    IsPullback.of_right (by rw [Category.assoc, hcf]; exact H₂)
      (by rw [Category.assoc, hcs]; exact hj₂.w)
      (IsPullback.of_hasPullback x f)
  obtain ⟨hP⟩ := ((CategoryTheory.BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hT) (Limits.BinaryCofan.mk (j₁ ≫ c) (j₂ ≫ c)) y₁ y₂ (Limits.pullback.snd x f)
    Q₁.w.symm Q₂.w.symm).mpr ⟨Q₁, Q₂⟩
  have hc : c = (hY.coconePointUniqueUpToIso hP).hom := by
    refine Limits.BinaryCofan.IsColimit.hom_ext hY ?_ ?_
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.left⟩).symm
    · exact (hY.comp_coconePointUniqueUpToIso_hom hP ⟨.right⟩).symm
  haveI : IsIso c := by rw [hc]; exact Iso.isIso_hom _
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) hcf hcs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfOpenBaseChangeEqPreimage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isPullback_of_open_part_eq_preimage :
    ∀ (S S₁ P G : Scheme.{0}) (p : P ⟶ S) (s : S₁ ⟶ S) (e : G ⟶ P) (c : G ⟶ S₁) (hw : e ≫ p = c ≫ s), IsOpenImmersion (Limits.pullback.lift e c hw) → ∀ V : P.Opens, (∀ w : ↥(Limits.pullback p s), Limits.pullback.fst p s w ∈ V ↔ w ∈ Set.range (Limits.pullback.lift e c hw)) → ∃ e' : G ⟶ V.toScheme, e' ≫ V.ι = e ∧ IsPullback e' c (V.ι ≫ p) s := by
  intro S S₁ P G p s e c hw hl V hV
  have hlf : Limits.pullback.lift e c hw ≫ Limits.pullback.fst p s = e :=
    Limits.pullback.lift_fst _ _ _
  have hls : Limits.pullback.lift e c hw ≫ Limits.pullback.snd p s = c :=
    Limits.pullback.lift_snd _ _ _
  generalize Limits.pullback.lift e c hw = l at hl hV hlf hls
  have hr : Set.range e ⊆ Set.range V.ι := by
    rintro _ ⟨g, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h := (hV (l g)).mpr ⟨g, rfl⟩
    rw [← Scheme.Hom.comp_apply, hlf] at h
    exact h
  have he' : IsOpenImmersion.lift V.ι e hr ≫ V.ι = e := IsOpenImmersion.lift_fac _ _ _
  generalize IsOpenImmersion.lift V.ι e hr = e' at he'
  have hcomm : e' ≫ V.ι ≫ p = c ≫ s := by rw [← Category.assoc, he', hw]
  have hk : ∀ t : PullbackCone (V.ι ≫ p) s, ∃ q : t.pt ⟶ G,
      q ≫ l = Limits.pullback.lift (t.fst ≫ V.ι) t.snd
        ((Category.assoc _ _ _).trans t.condition) := by
    intro t
    refine ⟨IsOpenImmersion.lift l _ ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    refine (hV _).mp ?_
    rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst, Scheme.Hom.comp_apply]
    exact (t.fst x).2
  choose q hq using hk
  refine ⟨e', he', ⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm q ?_ ?_ ?_⟩⟩
  · intro t
    rw [← cancel_mono V.ι, Category.assoc, he', ← hlf, ← Category.assoc, hq,
      Limits.pullback.lift_fst]
  · intro t
    conv_lhs => rw [← hls]
    rw [← Category.assoc, hq, Limits.pullback.lift_snd]
  · intro t m h₁ h₂
    rw [← cancel_mono l, hq]
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hlf, Limits.pullback.lift_fst, ← h₁, Category.assoc, he']
    · rw [Category.assoc, hls, Limits.pullback.lift_snd, h₂]

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSpMapQuotientSpanBaseChange
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotBaseChange

theorem isPushout_quot_span (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R)
    (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f})
    (hρ : ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π) :
    IsPushout (CommRingCat.ofHom π) (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π f}))) (CommRingCat.ofHom ρ) := by
  refine ⟨⟨by ext a; exact (congr($hρ a)).symm⟩, ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift (Ideal.span {π f}) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩
  · intro b hb
    have e : ∀ a, s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := fun a => congr($(s.condition) a)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [map_mul, e, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f), map_zero, mul_zero]
  · intro s
    ext b
    rfl
  · intro s
    ext a
    have e : s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := congr($(s.condition) a)
    have e2 : ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (π a) := congr($hρ a)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [e2, Ideal.Quotient.lift_mk, e]
  · intro s m h₁ _
    ext b
    have e : m.hom (Ideal.Quotient.mk _ b) = s.inl.hom b := congr($h₁ b)
    exact e

theorem isPullback_spMap_quot : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π → IsPullback (spMap (Ideal.Quotient.mk (Ideal.span {π f}))) (spMap ρ) (spMap π) (spMap (Ideal.Quotient.mk (Ideal.span {f}))) := by
  intro R R₀ _ _ π f ρ hρ
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot_span R R₀ π f ρ hρ)

end GlobalTheory.QuotBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayQProj

theorem finiteType_closure {K : Type} [CommRing K] {s : Set K} (hs : s.Finite) :
    (Int.castRingHom (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have e : Algebra.adjoin ℤ s ≃+* Subring.closure s :=
    RingEquiv.subringCongr (s := (Algebra.adjoin ℤ s).toSubring) (by rw [Algebra.adjoin_int]; rfl)
  have h' : Algebra.FiniteType ℤ (Subring.closure s) := h.equiv (AlgEquiv.ofRingEquiv (f := e) fun x => by simp)
  have := RingHom.finiteType_algebraMap.2 h'
  rwa [RingHom.eq_intCast' (algebraMap ℤ (Subring.closure s))] at this

theorem finiteType_cycAway (M : ℕ) : (Int.castRingHom (cycAway M)).FiniteType :=
  finiteType_closure (Set.toFinite _)

theorem isQProjOver_comp_spMap {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.FiniteType)
    {Y : Scheme.{0}} {s : Y ⟶ Sp B} (h : IsQProjOver s) : IsQProjOver (s ≫ spMap f) := by
  obtain ⟨_, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  have : LocallyOfFiniteType (spMap f) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hf
  exact (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB _).2 ⟨inferInstance, hL⟩

theorem isQProjOver_of_isFinite_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) :=
  fun M _ _ _ _ _ _ hs _ π _ =>
    isQProjOver_comp_of_isFinite π
      (isQProjOver_of_isPullback (IsPullback.of_hasPullback _ _) (isQProjOver_comp_spMap (finiteType_cycAway M) hs))

end GlobalTheory.CycAwayQProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientDualWeylEmbedsHighestWeightStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simpleSubquotient_dualWeyl_embeds_highestWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∃ mu : ι → ℕ → ℕ, (∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧ (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧ ∃ (e : alg O N lam) (z : Gm), IsProj O N lam τ (res N (mu τ)) e ∧ e • z ≠ 0) ∧ Embeds O N lam mu ϖ Gm := by
  first | exact @GlobalTheory.HighWt.simpleSubquot_embeds | exact GlobalTheory.HighWt.simpleSubquot_embeds | (intros; apply GlobalTheory.HighWt.simpleSubquot_embeds <;> assumption)
end

