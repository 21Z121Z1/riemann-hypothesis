import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsUnitIffMem

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitDet

theorem eq_of_im_hermForm_eq {g : ℕ} (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im) : A = B := by
  have h1 : ∀ z, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w hw
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact h1 z x hx
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1

theorem hermForm_mulVec {g : ℕ} (A h : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm A (h *ᵥ z) (h *ᵥ w) = hermForm (hᵀ * (A * h.map (starRingEnd ℂ))) z w := by
  have : star (h *ᵥ w) = h.map (starRingEnd ℂ) *ᵥ star w := by
    ext a; simp [Matrix.mulVec, dotProduct]
  rw [hermForm, hermForm, this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose]

theorem det_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, (∀ τ i, ‖dmin (M.X k).Gm x τ i‖ = 1) → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ a b, (hermForm Hm (Pf x a) (Pf x b)).im = (F.Di k).EF a b) → Hm.det = ((∏ j, (2 * ‖relab c σ (e j).1 (M.X k).ξ0‖) : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx hu Hm hHm
  obtain ⟨hl1, hl2, -⟩ := GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular E r (M.X k).p0 (M.X k).Ψ (M.X k).Gm (M.X k).Gm_herm
  obtain ⟨x₀, b, hb, hgr, hb1, rfl⟩ := hl1 x hx hu
  have hx₀ : x₀ ∈ (M.X k).dom := (hl2 x₀ hgr).1
  obtain ⟨h₀, -, hh, -, -, hdet, -⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x₀ hx₀ b hb
  replace hdet := hdet hb1
  obtain ⟨Pf', -, huniq, hper, -⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k
  obtain rfl := huniq Pf hPf
  have hspan := (hper x₀ hx₀).2.2.2.1
  obtain ⟨⟨idx, hty, -, hfr⟩, hp, -, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hD := GlobalTheory.UnitFrame.im_hermForm_eq E H (F.Di k) r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ
    (hB.type k).2 g idx (fun j => relab c σ (e j).1) hty hξ hpos (hφ φ fun _ => rfl).2 x₀ (Pf x₀)
    (fun v j => by rw [hPf, hfr]; rfl) (fun τ => by rw [← hp]; exact hgr τ)
  have key : h₀ᵀ * (Hm * h₀.map (starRingEnd ℂ)) =
      Matrix.diagonal fun j => ((2 * ‖(idx j).1.1 (-(M.X k).ξ0)‖ : ℝ) : ℂ) := by
    refine eq_of_im_hermForm_eq _ hspan _ _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [hD, ← hermForm_mulVec, ← hh, ← hh, hHm]
  have h1 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have h2 : h₀.det * starRingEnd ℂ h₀.det = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hdet]; simp
  have h3 : Hm.det = h₀.det * (Hm.det * starRingEnd ℂ h₀.det) := by
    linear_combination (-Hm.det) * h2
  rw [h3, h1, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hty j, map_neg, norm_neg]
  split_ifs
  · rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  · rfl

end GlobalTheory.UnitDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.LieBaseChange

open GlobalTheory.SqZero

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

def pushRHom (P : Type) [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P] :
    (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) →* (sp (R₀ := R) P ⟶ G) where
  toFun := pushR G
  map_one' := pushR_one G
  map_mul' y y' := by
    have h := map_mul (pushHom (isGrpPullback_pullback G (fB R R')) (sp (R₀ := R') P)) y y'
    exact (congrArg (iotaB ≫ ·) h).trans (MonObj.comp_mul _ _ _)

theorem isTan_iff_mem (w : sp (R₀ := R') (DualNumber R') ⟶ (Over.pullback (fB R R')).obj G) :
    IsTan w ↔ pushR G w ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)) := by
  have e : IsTan w ↔ spMap ((fstD R').restrictScalars R) ≫ pushR G w = 1 := by
    rw [← pushR_spMap, IsTan]
    exact ⟨fun h => by rw [h, pushR_one], fun h => pushR_inj G (by rw [h, pushR_one])⟩
  rw [e]
  exact ⟨mem_redKer_of_section _ ((Algebra.ofId R' (DualNumber R')).restrictScalars R)
    (fun a => rfl), fun h => comp_eq_one_of_mem_redKer h _ fun a ha => ha⟩

variable {G} {n : ℕ}

def bcVec (R' : Type) [CommRing R'] [Algebra R R'] (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    epsR R' ⟶ (Over.pullback (fB R R')).obj G :=
  pullR (R' := R') G (spMap (dualMapA R R') ≫ v i)

theorem pushR_bcVec (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    pushR G (bcVec R' v i) = spMap (dualMapA R R') ≫ v i := pushR_pullR G _

theorem bcVec_left_fst (v : Fin n → (epsR R ⟶ G)) (i : Fin n) :
    (bcVec R' v i).left ≫ pullback.fst G.hom (fB R R') =
      Geo.Tor.spMap (dualMapR (algebraMap R R')) ≫ (v i).left := by
  rw [← pushR_left, pushR_bcVec]
  rfl

theorem pushR_prodPts [IsCommMonObj G] (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R') :
    pushR G (prodPts c (bcVec R' v)) =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) := by
  refine (map_list_prod (pushRHom G (DualNumber R')) _).trans ?_
  rw [List.map_ofFn, List.prod_ofFn, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  change pushR G (spMap _ ≫ _) = _
  rw [pushR_spMap, pushR_bcVec, ← Category.assoc, spMap_comp]
  congr 2
  refine DualNumber.algHom_ext ?_
  rw [epsTo_eps, AlgHom.comp_apply]
  change TrivSqZeroExt.map _ (dualMapA R R' (inr 1)) = _
  rw [dualMapA_inr, TrivSqZeroExt.map_inr]
  simp

theorem isLieBasis_bcVec_of [IsCommMonObj G] {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
    (inj : ∀ c c' : Fin n → R',
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) =
      lieExp v (fun i => (inr (c' i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) →
        c = c')
    (surj : ∀ y ∈ redKer G (RingHom.ker ((fstD R').restrictScalars R)), ∃ c : Fin n → R', y =
      lieExp v (fun i => (inr (c i) : DualNumber R')) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)) :
    IsLieBasis (bcVec R' v) := by
  refine ⟨fun i => (isTan_iff _).1 ((isTan_iff_mem G _).2 ?_), fun w hw => ?_⟩
  · rw [pushR_bcVec]
    refine mem_redKer_of_section ((fstD R').restrictScalars R)
      ((Algebra.ofId R' (DualNumber R')).restrictScalars R) (fun a => rfl) ?_
    have : ((fstD R').restrictScalars R).comp (dualMapA R R') = (Algebra.ofId R R').comp (fstD R) := by
      refine DualNumber.algHom_ext ?_
      change (dualMapA R R' (inr 1)).fst = algebraMap R R' 0
      rw [dualMapA_inr]; simp
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, (isTan_iff _).2 (hv i),
      comp_one']
  · obtain ⟨c, hc⟩ := surj _ ((isTan_iff_mem G _).1 ((isTan_iff _).2 hw))
    refine ⟨c, (isLieComb_iff _ _ _).2 (pushR_inj G (by rw [hc, pushR_prodPts])), fun c' hc' => ?_⟩
    refine inj _ _ ?_
    rw [← hc, (isLieComb_iff _ _ _).1 hc', pushR_prodPts]

theorem isLieBasis_bcVec [IsCommMonObj G] [Smooth G.hom] {v : Fin n → (epsR R ⟶ G)}
    (hv : IsLieBasis v) : IsLieBasis (bcVec R' v) := by
  obtain ⟨h₁, h₂⟩ := expBij (DualNumber R') hv (RingHom.ker ((fstD R').restrictScalars R))
    (ker_fst_sq (R := R) (S := R') R')
  refine isLieBasis_bcVec_of hv.1 (fun c c' h => funext fun i => ?_) fun y hy => ?_
  · exact congrArg TrivSqZeroExt.snd
      (congrFun (h₁ _ _ (fun i => inr_mem_kerD (c i)) (fun i => inr_mem_kerD (c' i)) _ _ h) i)
  · obtain ⟨c, hc, hcJ, e⟩ := h₂ y hy
    have hc' : ∀ i, c i = inr (c i).snd := fun i =>
      have h0 : (c i).fst = 0 := hcJ i
      TrivSqZeroExt.ext h0 rfl
    exact ⟨fun i => (c i).snd, e.trans (lieExp_congr v hc' _ _)⟩

end GlobalTheory.LieBaseChange

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (spMap)

theorem exists_isLieBasis_baseChange (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R')
    (G : Over (Sp R)) (G' : Over (Sp R')) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) (hs : Smooth G.hom) (n : ℕ)
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) :
    ∃ v' : Fin n → (epsR R' ⟶ G'), IsLieBasis v' ∧
      ∀ i, (v' i).left ≫ φ = Geo.Tor.spMap (Chart.dualMapR f) ≫ (v i).left := by
  let _ := f.toAlgebra
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G (fB R R'))
  refine ⟨fun i => LieBaseChange.bcVec R' v i ≫ e.inv, isLieBasis_iso e ?_, fun i => ?_⟩
  · simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using
      LieBaseChange.isLieBasis_bcVec (R' := R') hv
  · rw [← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact LieBaseChange.bcVec_left_fst v i

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralClosureFiniteLocalCompleteMixedChar
section
open IsLocalRing

namespace GlobalTheory

open IsLocalRing in

theorem _root_.GlobalTheory.finite_normalisation_of_finite_over_normal (A S : Type) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing S] [IsDomain S] [CharZero S]
    [Algebra A S] [FaithfulSMul A S] [Module.Finite A S] :
    Module.Finite S (integralClosure S (FractionRing S)) := by
  haveI : FaithfulSMul A (FractionRing S) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A S (FractionRing S)]
    exact (IsFractionRing.injective S _).comp (FaithfulSMul.algebraMap_injective A S))
  letI : Algebra (FractionRing A) (FractionRing S) := FractionRing.liftAlgebra A _
  haveI := FractionRing.isScalarTower_liftAlgebra A (FractionRing S)
  haveI : CharZero (FractionRing S) := charZero_of_injective_algebraMap (IsFractionRing.injective S _)
  haveI : CharZero (FractionRing A) := (algebraMap (FractionRing A) (FractionRing S)).charZero
  haveI : FiniteDimensional (FractionRing A) (FractionRing S) := inferInstance
  haveI : IsIntegralClosure (integralClosure S (FractionRing S)) A (FractionRing S) := by
    refine ⟨Subtype.val_injective, fun {x} => ⟨fun h => ⟨⟨x, h.tower_top⟩, rfl⟩, ?_⟩⟩
    rintro ⟨y, rfl⟩
    exact isIntegral_trans (R := A) (A := S) (y : FractionRing S) y.2
  haveI : Module.Finite A (integralClosure S (FractionRing S)) :=
    IsIntegralClosure.finite A (FractionRing A) (FractionRing S) _
  exact Module.Finite.of_restrictScalars_finite A S _

open IsLocalRing in
private theorem isPrecomplete_of_finite_module {R M : Type*} [CommRing R] {I : Ideal R} [hR : IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hpow : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have key : ∀ n (x : M), x ∈ (I ^ n • ⊤ : Submodule R M) →
      ∃ c : Fin k → R, (∀ j, c j ∈ I ^ n) ∧ ∑ j, c j • g j = x := by
    intro n x hx
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, by simp [Finsupp.sum_fintype]⟩
  refine ⟨fun {f} hf => ?_⟩
  have hd : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := fun n => by
    have := (hf (Nat.le_succ n))
    rw [SModEq.sub_mem] at this
    simpa using neg_mem this
  choose c hcI hcsum using fun n => key n _ (hd n)
  have hs : ∀ j, ∃ a : R, ∀ n, (∑ i ∈ Finset.range n, c i j) ≡ a [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro j
    refine hR.prec' _ fun {m n} hmn => ?_
    rw [SModEq.sub_mem, hpow]
    have : ∑ i ∈ Finset.range m, c i j - ∑ i ∈ Finset.range n, c i j =
        -∑ i ∈ Finset.Ico m n, c i j := by
      rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
    rw [this]
    exact neg_mem (Ideal.sum_mem _ fun i hi =>
      Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hcI i j))
  choose a ha using hs
  refine ⟨f 0 + ∑ j, a j • g j, fun n => ?_⟩
  have hfn : f n = f 0 + ∑ j, (∑ i ∈ Finset.range n, c i j) • g j := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, hcsum n]
      rw [← add_assoc, ← ih]
      abel
  rw [SModEq.sub_mem, hfn, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have := (SModEq.sub_mem.1 (ha j n))
  rw [hpow] at this
  exact Submodule.smul_mem_smul this Submodule.mem_top

open IsLocalRing in
open Polynomial in
private theorem isLocalRing_of_finite_domain_over_complete (S C : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S] [CommRing C] [IsDomain C] [Algebra S C]
    [Module.Finite S C] : IsLocalRing C := by
  set I : Ideal C := (maximalIdeal S).map (algebraMap S C) with hI
  haveI : IsPrecomplete (maximalIdeal S) C := isPrecomplete_of_finite_module
  haveI : IsAdicComplete (maximalIdeal S) C := {}
  haveI : IsAdicComplete I C := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  have hIM : ∀ M : Ideal C, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := S) M)).ge
  haveI : IsArtinianRing (C ⧸ I) := by
    letI := Ideal.Quotient.field (maximalIdeal S)
    haveI : Module.Finite (S ⧸ maximalIdeal S) (C ⧸ I) :=
      Module.Finite.of_restrictScalars_finite S _ _
    exact IsArtinianRing.of_finite (S ⧸ maximalIdeal S) _
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨M₁, hM₁⟩ := Ideal.exists_maximal C
  refine ⟨M₁, hM₁, fun M₂ hM₂ => ?_⟩
  by_contra hne
  obtain ⟨x, hx₂, hx₁⟩ : ∃ x ∈ M₂, x ∉ M₁ := by
    by_contra! h
    exact hne (hM₂.eq_of_le hM₁.ne_top h)
  set u := Ideal.Quotient.mk I x with hu
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := C ⧸ I) (M := C ⧸ I)
    ⟨fun n => OrderDual.toDual (Ideal.span {u ^ n}),
      fun a b hab => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow u hab)⟩
  set m := N + 1 with hmdef
  have hm : u ^ m ∈ Ideal.span {u ^ (m + 1)} := by
    have h₁ := hN m (by omega)
    have h₂ := hN (m + 1) (by omega)
    have : Ideal.span {u ^ m} = Ideal.span {u ^ (m + 1)} := by
      exact congrArg OrderDual.ofDual (h₁.symm.trans h₂)
    rw [← this]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hm
  have hpow : ∀ j, u ^ m = u ^ (m + j) * v ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih, pow_add u m j, ← hv]
      ring
  have he : (u ^ m * v ^ m) * (u ^ m * v ^ m) = u ^ m * v ^ m := by
    calc (u ^ m * v ^ m) * (u ^ m * v ^ m) = (u ^ (m + m) * v ^ m) * v ^ m := by ring
      _ = u ^ m * v ^ m := by rw [← hpow m]
  have hue : u ^ m = u ^ m * (u ^ m * v ^ m) := by
    calc u ^ m = u ^ (m + m) * v ^ m := hpow m
      _ = u ^ m * (u ^ m * v ^ m) := by ring
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
  set a₀ := x ^ m * y ^ m with ha₀def
  have hmk : Ideal.Quotient.mk I a₀ = u ^ m * Ideal.Quotient.mk I y ^ m := by
    simp [ha₀def, hu]
  have hmon : (X ^ 2 - X : C[X]).Monic := by monicity!
  have heval : (X ^ 2 - X : C[X]).eval a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow, hmk]
    rw [sq, he, sub_self]
  have hder : (derivative (X ^ 2 - X : C[X])).eval a₀ = 2 * a₀ - 1 := by
    simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
      eval_pow, eval_X, eval_one]
    norm_num
  have hunit : IsUnit (Ideal.Quotient.mk I ((derivative (X ^ 2 - X : C[X])).eval a₀)) := by
    rw [hder, map_sub, map_mul, hmk, map_one, map_ofNat]
    exact (Units.mkOfMulEqOne _ (2 * (u ^ m * Ideal.Quotient.mk I y ^ m) - 1)
      (by linear_combination 4 * he)).isUnit
  obtain ⟨a, ha, haa₀⟩ := HenselianRing.is_henselian (I := I) _ hmon a₀ heval hunit
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  have hx₂m : a₀ ∈ M₂ := M₂.mul_mem_right _ (M₂.pow_mem_of_mem hx₂ m (by omega))
  rcases mul_eq_zero.1 ha' with h0 | h1
  · subst h0
    have ha₀I : a₀ ∈ I := by simpa using neg_mem haa₀
    have hxm : x ^ m - x ^ m * a₀ ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk, map_pow, ← hu, ← hue,
        sub_self]
    have : x ^ m ∈ M₁ := by
      have h := hIM M₁ hM₁ hxm
      have h' := M₁.mul_mem_left (x ^ m) (hIM M₁ hM₁ ha₀I)
      simpa using M₁.add_mem h h'
    exact hx₁ (hM₁.isPrime.mem_of_pow_mem m this)
  · have h1' : a = 1 := sub_eq_zero.1 h1
    subst h1'
    have : (1 : C) ∈ M₂ := by
      have h := hIM M₂ hM₂ haa₀
      simpa using M₂.add_mem h hx₂m
    exact hM₂.ne_top ((Ideal.eq_top_iff_one _).2 this)

open IsLocalRing in
theorem _root_.GlobalTheory.normalisation_finite_local_complete_of_mixedChar :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      Module.Finite S (integralClosure S (FractionRing S)) ∧
        ∃ _ : IsLocalRing (integralClosure S (FractionRing S)),
          IsNoetherianRing (integralClosure S (FractionRing S)) ∧
          IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S)))
            (integralClosure S (FractionRing S)) := by
  intro S _ _ _ _ p hp hpm hS hSc
  obtain ⟨A, _, _, _, i, hi, hfin, hAn, hAic, hAc⟩ :=
    _root_.GlobalTheory.CohenStructure.exists_finite_injective_of_isAdicComplete S p hp hpm hS hSc
  letI : Algebra A S := i.toAlgebra
  haveI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  haveI : Module.Finite A S := hfin
  haveI := hAn
  haveI := hAic
  haveI := hS
  haveI := hSc
  haveI hC : Module.Finite S (integralClosure S (FractionRing S)) := _root_.GlobalTheory.finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing (integralClosure S (FractionRing S)) := isLocalRing_of_finite_domain_over_complete S _
  haveI : IsNoetherianRing (integralClosure S (FractionRing S)) := isNoetherian_of_tower S inferInstance
  exact ⟨hC, inferInstance, inferInstance,
    _root_.GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite S _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonzeroLocusSecPw
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.ProjAffineLoci

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_res gs_mul fn_ext)
open TopologicalSpace

variable {X : Scheme.{0}} {R : Type} [CommRing R]

def zeroSec (H : LB X) : LB.Sec H := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩

def secPw {L : LB X} (σ : LB.Sec L) (d : ℕ) : LB.Sec (pw L d) where
  f := fun k => σ.f k ^ d
  compat := fun i j => by
    have h := congrArg (· ^ d) (σ.compat i j)
    simp only [mul_pow, ← map_pow] at h
    refine h.trans (congrArg (· * _) ?_)
    change _ = ((L.g i j ^ (d : ℤ) : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j))
    rw [zpow_natCast, Units.val_pow_eq_pow_val]

theorem chart (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} (hH : H.IsLB) {I : Type} (t : I → LB.Sec H) (i : I)
    {W : X.Opens} (e : nonzeroLocus (t i) = W) {n : ℕ} (b : Fin n → Γ(X, W))
    (hb : Function.Surjective (MvPolynomial.eval₂Hom (cst f W) b)) (c : Fin n → I)
    (hc : ∀ l k, rs X (inf_le_right : W ⊓ H.U k ≤ H.U k) ((t (c l)).f k) =
      rs X (inf_le_left : W ⊓ H.U k ≤ W) (b l) * rs X (inf_le_right : W ⊓ H.U k ≤ H.U k) ((t i).f k)) :
    ∃ r : I → Γ(X, nonzeroLocus (t i)),
      (∀ j k, rs X (inf_le_right : nonzeroLocus (t i) ⊓ H.U k ≤ H.U k) ((t j).f k) =
        rs X (inf_le_left : nonzeroLocus (t i) ⊓ H.U k ≤ nonzeroLocus (t i)) (r j) *
          rs X (inf_le_right : nonzeroLocus (t i) ⊓ H.U k ≤ H.U k) ((t i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (t i))) r) := by
  subst e
  choose ρ hρ using fun j => GlobalTheory.VeryAmplePow.exists_ratio (t i) (t j)
  refine ⟨ρ, fun j k => fn_ext fun y hy => ?_, fun y => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hρ j _ (𝟙 X) y k hy.1 hy.2).trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _))).symm)
  · have hρb : ∀ l, ρ (c l) = b l := fun l => fn_ext fun z hz => by
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show z ∈ ⨆ k, H.U k by rw [hH.cover]; trivial)
      have hm : (𝟙 X : X ⟶ X) z ∈ nonzeroLocus (t i) ⊓ H.U k := ⟨hz, hk⟩
      have h₁ := (gs_res _ z _ hm _).symm.trans ((congrArg (gs (𝟙 X) z _) (hc l k)).trans
        ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ z _ hm _) (gs_res _ z _ hm _))))
      have u := (GlobalTheory.VeryAmplePow.isUnit_iff_mem (t i) (𝟙 X) z hk).2 hz
      exact u.mul_left_inj.1 ((hρ (c l) _ (𝟙 X) z k hz hk).symm.trans h₁)
    obtain ⟨p, rfl⟩ := hb y
    refine ⟨MvPolynomial.rename c p, ?_⟩
    rw [MvPolynomial.eval₂Hom_rename]
    congr 2
    exact funext hρb

end GlobalTheory.ProjAffineLoci
end
end

