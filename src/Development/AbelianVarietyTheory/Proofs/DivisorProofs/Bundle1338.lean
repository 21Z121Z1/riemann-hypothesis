import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.RatSecCycle

open GlobalTheory.Cartier.CartierDiv

theorem exists_sec_divOfSec_eq {X : Scheme.{0}} [IsIntegral X] (E : CartierDiv X) (hE : E.Eff) :
    ∃ (s : (toLB E).Sec) (hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s),
      divOfSec (isLB_toLB E) s hs = E := by
  have h := presents_toLB E
  obtain ⟨s, hs1⟩ := h.exists_rat_eq (f := 1) (mem_sections.2 hE)
  have hs : genericPoint X ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s :=
    (h.generatesAt_rat_iff s).1 (hs1 ▸ E.generatesAt_genericPoint one_ne_zero)
  refine ⟨s, hs, Presents.unique (presents_divOfRatSec (isLB_toLB E) _) ⟨isLB_toLB E,
    isRatSec_ratOfSec s hs, fun i x hx => ?_⟩⟩
  have e : ratOfSec s hs i = i.1.2 := Units.ext (by
    rw [val_ratOfSec (gen_mem hx), ← h.rat_mul s i (gen_mem hx), hs1, one_mul])
  rw [e]
  exact h.isEqn i x hx

end GlobalTheory.RatSecCycle

open GlobalTheory.Cartier.CartierDiv in

theorem GlobalTheory.ratSec_cycle_formula : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ X) → ∀ (n : ℕ), topologicalKrullDim X ≤ (n + 1 : ℕ) → ∀ (M : LB X) (hM : M.IsLB) (P : Fin n → LB X), (∀ i, (P i).IsLB) → ∀ (r : M.ι → X.functionFieldˣ) (hr : IsRatSec M r), interNum κ (structureModule X) (Fin.cons M P : Fin (n + 1) → LB X) = ∑ᶠ w, (divOfRatSec hM hr).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ _ _ hp n hn M hM P hP r hr
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  set D := divOfRatSec hM hr with hD
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨E, hE, hDE⟩ := GlobalTheory.T.exists_effective_cartierDivisor_add_effective X H hH D
  have key : ∀ E' : CartierDiv X, E'.Eff →
      interNum κ (structureModule X) (Fin.cons (toLB E') P : Fin (n + 1) → LB X) =
        ∑ᶠ w, E'.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
    intro E' hE'
    obtain ⟨s, hs, e⟩ := GlobalTheory.RatSecCycle.exists_sec_divOfSec_eq E' hE'
    have := GlobalTheory.T.intersectionNumber_globalSection_eq_sum_cycle κ X hp n hn (toLB E') (isLB_toLB E') P hP s hs
    rw [e] at this
    exact this
  have hv := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ X) (structureModule X) hp
    (d := n + 1) (by rw [QCoh.suppDim_structureModule]; exact hn)
  have hc : CechPic.cls (toLB (D + E)) (isLB_toLB (D + E)) =
      CechPic.cls M hM + CechPic.cls (toLB E) (isLB_toLB E) := by
    rw [← toPic_apply, ← toPic_apply, map_add, (presents_divOfRatSec hM hr).toPic_eq]
  have ha := hv.interNum_cons_of_cls_eq_add le_rfl hP (isLB_toLB (D + E)) hM (isLB_toLB E) hc
  rw [key _ hDE, key _ hE] at ha
  have hfin : ∀ F : CartierDiv X, Function.HasFiniteSupport
      (fun w => F.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) :=
    fun F => (F.finite_support_mult).subset (Function.support_mul_subset_left _ _)
  have e2 : (∑ᶠ w, (D + E).mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) =
      (∑ᶠ w, D.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P) +
        ∑ᶠ w, E.mult w * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
    simp only [mult_add, add_mul]
    exact finsum_add_distrib (hfin D) (hfin E)
  rw [e2] at ha
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (C H : ∀ v, Subgroup (Y v)), (∀ v, (H v).relIndex (C v) ≠ 0) → (∀ᶠ v in cofinite, C v ≤ H v) → (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  first | exact @GlobalTheory.RelIdxRestr.relIndex_iInf_comap | exact GlobalTheory.RelIdxRestr.relIndex_iInf_comap | (intros; apply GlobalTheory.RelIdxRestr.relIndex_iInf_comap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationIntertwinesLie
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin.RightTr

variable {n : ℕ} {G : Type} [Group G] {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}

theorem isUni_exp (hJ : IsUnit J.det) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsSkew J X) :
    IsUni J (NormedSpace.exp X) := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  change (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
    neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem isSkew_smul {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) : IsSkew J (t • Z) := by
  unfold IsSkew at *
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hZ, smul_zero]

theorem isUnit_det_of_isUni (hJ : IsUnit J.det) {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) : IsUnit u.det := by
  have h : (uᴴ * J * u).det = J.det := congrArg Matrix.det hu
  rw [det_mul] at h
  exact isUnit_of_mul_isUnit_right (h ▸ hJ)

theorem isSkew_conj_of {u Z W : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (h : W * u = u * Z) :
    uᴴ * (Wᴴ * J + J * W) * u = Zᴴ * J + J * Z := by
  have h' : uᴴ * Wᴴ = Zᴴ * uᴴ := by rw [← conjTranspose_mul, h, conjTranspose_mul]
  unfold IsUni at hu
  calc uᴴ * (Wᴴ * J + J * W) * u = (uᴴ * Wᴴ) * J * u + uᴴ * J * (W * u) := by noncomm_ring
    _ = Zᴴ * (uᴴ * J * u) + (uᴴ * J * u) * Z := by rw [h, h']; noncomm_ring
    _ = _ := by rw [hu]

theorem isSkew_inv_conj (hJ : IsUnit J.det) {u Z : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (hZ : IsSkew J Z) :
    IsSkew J (u⁻¹ * Z * u) := by
  have hd := isUnit_det_of_isUni hJ hu
  have := isSkew_conj_of (W := Z) (Z := u⁻¹ * Z * u) hu
    (by rw [mul_assoc, mul_nonsing_inv_cancel_left _ _ hd])
  unfold IsSkew at *
  rw [← this, hZ, mul_zero, zero_mul]

theorem isSkew_conj (hJ : IsUnit J.det) {u Z : Matrix (Fin n) (Fin n) ℂ} (hu : IsUni J u) (hZ : IsSkew J Z) :
    IsSkew J (u * Z * u⁻¹) := by
  have hd := isUnit_det_of_isUni hJ hu
  have hd' : IsUnit uᴴ.det := by rw [det_conjTranspose]; exact hd.star
  have := isSkew_conj_of (W := u * Z * u⁻¹) (Z := Z) hu
    (by rw [nonsing_inv_mul_cancel_right _ _ hd])
  unfold IsSkew at *
  rw [hZ] at this
  have h2 := congrArg (fun M => (uᴴ)⁻¹ * M * u⁻¹) this
  simp only [mul_zero, zero_mul] at h2
  rwa [mul_assoc uᴴ, nonsing_inv_mul_cancel_left _ _ hd', mul_nonsing_inv_cancel_right _ _ hd] at h2

theorem lineOf_zero (hs : IsMulOn J s) (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  have h1 : IsUni J 1 := by simp [IsUni]
  have := hs 1 1 h1 h1
  rw [mul_one] at this
  rw [lineOf, zero_smul, NormedSpace.exp_zero]
  exact left_eq_mul.1 this

theorem lineOf_mul (hJ : IsUnit J.det) (hs : IsMulOn J s) {u : Matrix (Fin n) (Fin n) ℂ} {b : G} (hu : IsUni J u)
    (hb : ∀ v, IsUni J v → b * s v = s v * b) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) :
    lineOf s Z t * (s u * b) = (s u * b) * lineOf s (u⁻¹ * Z * u) t := by
  have hd := isUnit_det_of_isUni hJ hu
  have h1 := isUni_exp hJ (isSkew_smul hZ t)
  have h2 := isUni_exp hJ (isSkew_smul (isSkew_inv_conj hJ hu hZ) t)
  have e : t • (u⁻¹ * Z * u) = u⁻¹ * (t • Z) * u := by rw [mul_smul_comm, smul_mul_assoc]
  unfold lineOf
  rw [mul_assoc (s u), hb _ h2, ← mul_assoc, ← mul_assoc, ← hs _ _ h1 hu, ← hs _ _ hu h2, e,
    Matrix.exp_conj' _ _ ((isUnit_iff_isUnit_det u).2 hd), mul_assoc u⁻¹, mul_nonsing_inv_cancel_left _ _ hd]

theorem prod_ofFn_mul (c : G) : ∀ (k : ℕ) (x y : Fin k → G), (∀ i, x i * c = c * y i) →
    (List.ofFn x).prod * c = c * (List.ofFn y).prod := by
  intro k
  induction k with
  | zero => intro x y _; simp
  | succ k ih =>
    intro x y h
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      ih _ _ (fun i => h i.succ), ← mul_assoc, h, mul_assoc]

theorem exists_skew_add (hH : Jᴴ = J) (hJ : IsUnit J.det) (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A B, IsSkew J A ∧ IsSkew J B ∧ Y = A + Complex.I • B := by
  have e1 : (J⁻¹ * Yᴴ * J)ᴴ * J = J * Y := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
      ← mul_assoc, nonsing_inv_mul_cancel_right _ _ hJ]
  have e2 : J * (J⁻¹ * Yᴴ * J) = Yᴴ * J := by
    rw [mul_assoc, mul_nonsing_inv_cancel_left _ _ hJ]
  generalize J⁻¹ * Yᴴ * J = Y' at e1 e2
  refine ⟨(1 / 2 : ℂ) • (Y - Y'), (-Complex.I / 2) • (Y + Y'), ?_, ?_, ?_⟩
  · unfold IsSkew
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [conjTranspose_smul, this, conjTranspose_sub, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, e1, e2]
    module
  · unfold IsSkew
    have : star (-Complex.I / 2 : ℂ) = -(-Complex.I / 2) := by simp; ring
    rw [conjTranspose_smul, this, conjTranspose_add, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, e1, e2]
    module
  · have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
    rw [smul_smul, this]
    module

theorem exists_rightTranslation : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ (u : Matrix (Fin n) (Fin n) ℂ) (b : G), IsUni J u → (∀ v, IsUni J v → b * s v = s v * b) → ∃ r : Module.End ℂ (smLoc J s), (∀ (f : smLoc J s) (g : G), (r f).1 g = f.1 (g * (s u * b))) ∧ ∀ Y, r * ρ Y = ρ (u * Y * u⁻¹) * r := by
  intro n G _ J s hH hJ hs ρ hρ u b hu hb
  have hd := isUnit_det_of_isUni hJ hu
  let r : Module.End ℂ (smLoc J s) :=
    { toFun := fun f => ⟨fun g => f.1 (g * (s u * b)), fun k Z hZ g => by
        have h := f.2 k (fun i => u⁻¹ * Z i * u) (fun i => isSkew_inv_conj hJ hu (hZ i)) (g * (s u * b))
        convert h using 2 with t
        beta_reduce
        rw [mul_assoc g, mul_assoc g, prod_ofFn_mul _ _ _ _ fun i => lineOf_mul hJ hs hu hb (hZ i) (t i)]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have key : ∀ Z, IsSkew J Z → r * ρ Z = ρ (u * Z * u⁻¹) * r := by
    intro Z hZ
    refine LinearMap.ext fun f => Subtype.ext (funext fun g => ?_)
    have h1 := hρ Z hZ f (g * (s u * b)) 0
    have h2 := hρ _ (isSkew_conj hJ hu hZ) (r f) g 0
    rw [lineOf_zero hs, mul_one] at h1 h2
    refine h1.unique ?_
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
    change f.1 (g * (s u * b) * lineOf s Z τ) = f.1 (g * lineOf s (u * Z * u⁻¹) τ * (s u * b))
    rw [mul_assoc g (lineOf _ _ _), lineOf_mul hJ hs hu hb (isSkew_conj hJ hu hZ), ← mul_assoc u⁻¹,
      nonsing_inv_mul_cancel_right _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_assoc g]
  refine ⟨r, fun _ _ => rfl, fun Y => ?_⟩
  obtain ⟨A, B, hA, hB, rfl⟩ := exists_skew_add hH hJ Y
  rw [mul_add u, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_add, map_smul, map_smul, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, key A hA, key B hB]

end GlobalTheory.TorFin.RightTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystem
section
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.ConeDim

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {N : ℕ}

theorem isAlgebraic_of_closure_eq_top (y : Fin N → Ω) (hy : y ≠ 0)
    (hgen : Subfield.closure (Set.range (algebraMap k Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤)
    (A : Subalgebra k (Polynomial Ω)) (hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A) :
    Algebra.IsAlgebraic A (Polynomial Ω) := by
  classical
  let ι : Polynomial Ω →+* FractionRing (Polynomial Ω) := algebraMap _ _
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let L : Subfield (FractionRing (Polynomial Ω)) := Subfield.closure (ι '' (A : Set (Polynomial Ω)))
  have hA : ∀ a ∈ A, ι a ∈ L := fun a ha => Subfield.subset_closure ⟨a, ha, rfl⟩
  have hne : ∀ j, y j ≠ 0 → ι (Polynomial.X * Polynomial.C (y j)) ≠ 0 := fun j hj =>
    (map_ne_zero_iff ι hι).2 (mul_ne_zero Polynomial.X_ne_zero (Polynomial.C_ne_zero.2 hj))
  let M : Subfield Ω := L.comap (ι.comp Polynomial.C)
  have hM : M = ⊤ := by
    refine top_unique (hgen ▸ Subfield.closure_le.2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨i, j, rfl⟩)
    · show ι (Polynomial.C (algebraMap k Ω c)) ∈ L
      rw [← Polynomial.algebraMap_apply]
      exact hA _ (A.algebraMap_mem c)
    · show ι (Polynomial.C (y i / y j)) ∈ L
      by_cases hj : y j = 0
      · rw [hj, div_zero, Polynomial.C_0, map_zero]
        exact zero_mem L
      · have e : ι (Polynomial.C (y i / y j)) =
            ι (Polynomial.X * Polynomial.C (y i)) / ι (Polynomial.X * Polynomial.C (y j)) := by
          rw [eq_div_iff (hne j hj), ← map_mul]
          congr 1
          rw [mul_left_comm, ← Polynomial.C_mul, div_mul_cancel₀ _ hj]
        rw [e]
        exact div_mem (hA _ (hXy i)) (hA _ (hXy j))
  have hC : ∀ c, ι (Polynomial.C c) ∈ L := fun c => by
    have h : c ∈ M := hM ▸ Subfield.mem_top c
    exact h
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have hX : ι Polynomial.X ∈ L := by
    have e : ι Polynomial.X = ι (Polynomial.X * Polynomial.C (y j)) * ι (Polynomial.C (y j)⁻¹) := by
      rw [← map_mul, mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hj, Polynomial.C_1, mul_one]
    rw [e]
    exact mul_mem (hA _ (hXy j)) (hC _)
  have hall : ∀ p, ι p ∈ L := fun p => by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact mul_mem (hC c) (pow_mem hX n)
  have hcl : Subring.closure (ι '' (A : Set (Polynomial Ω))) ≤ (A.toSubring.map ι) :=
    Subring.closure_le.2 (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)
  refine ⟨fun p => ?_⟩
  obtain ⟨_, ha₀, _, hb₀, hab⟩ := Subfield.mem_closure_iff.1 (hall p)
  obtain ⟨a, ha, rfl⟩ := hcl ha₀
  obtain ⟨b, hb, rfl⟩ := hcl hb₀
  by_cases hb0 : b = 0
  · rw [hb0, map_zero, div_zero, eq_comm, map_eq_zero_iff ι hι] at hab
    rw [hab]
    exact isAlgebraic_zero
  · have e : b * p = a := by
      apply hι
      rw [map_mul, ← hab, mul_div_cancel₀ _ ((map_ne_zero_iff ι hι).2 hb0)]
    refine ⟨Polynomial.C (⟨b, hb⟩ : A) * Polynomial.X - Polynomial.C (⟨a, ha⟩ : A), fun h => hb0 ?_, ?_⟩
    · have := congrArg (fun q => Polynomial.coeff q 1) h
      simp at this
      exact congrArg Subtype.val this
    · simp [e]

theorem ringKrullDim_imageIdeal_of_birational : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety →
    S.BasePointFree → S.Birational →
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = ((S.D + 1 : ℕ) : WithBot ℕ∞) := by
  intro k _ S h hb ⟨η, hη, hr⟩
  have := HeightExists.isIntegral h
  let Ω := S.Y.residueField η
  letI : Algebra k Ω := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt Ω := ⟨resPt η, S.comp_str _⟩
  set y : Fin S.N → Ω := S.coords (resPt η) with hy
  have hI : S.imageIdeal = coneIdeal k y :=
    imageIdeal_eq_coneIdeal_of_generic k Ω S x (by rw [ptOf_resPt]; exact hη) 1 y one_ne_zero
      (one_smul _ _).symm
  have hD : Algebra.trdeg k Ω = S.D :=
    (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth η
      fun z hz => (hz.antisymm (hη.specializes trivial)).eq).2
  rw [hI]
  have := isPrime_coneIdeal (K := k) y
  refine ringKrullDim_eq_of_trdeg_eq k _ ?_
  let f := Ideal.kerLiftAlg (coneMap k y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg k (MvPolynomial (Fin S.N) k ⧸ coneIdeal k y) = Algebra.trdeg k A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := ConeDim.isAlgebraic_of_closure_eq_top y (hb.coords_ne_zero _) hr A hXy
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (Polynomial Ω), ← trdeg_add_eq k Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain, hD]
  norm_cast

end GlobalTheory.Adelic.ConeDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLocalizationGraphIdealMinimalPrimeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_localization_graphIdeal_minimalPrime : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (k : ℕ) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) → (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  𝔭 ∈ (graphIdeal E R π ρ).minimalPrimes →
  ringKrullDim (locAt (L := L) 𝔭) = k + 1 := by
  first | exact @GlobalTheory.GraphLocal.dim_locAt_graph | exact GlobalTheory.GraphLocal.dim_locAt_graph | (intros; apply GlobalTheory.GraphLocal.dim_locAt_graph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeLinearFactorsRegroup
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.multiset_map_prod_finset_sum {α β γ : Type} [CommMonoid γ] (F : α → γ) (s : Finset β)
    (m : β → Multiset α) :
    ((∑ i ∈ s, m i).map F).prod = ∏ i ∈ s, ((m i).map F).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add, Multiset.prod_add, ih]

theorem GlobalTheory.satake_linear_factors_regroup : ∀ (K : Type) [Field K] (ι : K ≃+* ℂ) (c : ℕ) (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ) (T : Multiset ℂˣ) (q : ℕ),
  q ≠ 0 → ∀ e : ℂ,
  ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * (q : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) = T.map (fun z => (z : ℂ)) →
  (T.map fun z : ℂˣ => Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ e))).prod =
    ∏ i, ∏ k : Fin (d i), ((S i).map fun z : ℂˣ =>
      Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ (e + (((d i : ℂ) - 1) / 2 - (k : ℕ)))))).prod := by
  intro K _ ι c d S T q hq e hT
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  set F : ℂ → Polynomial K := fun u => Polynomial.X - Polynomial.C (ι.symm (u * (q : ℂ) ^ e)) with hF
  have h1 : (T.map fun z : ℂˣ => Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ e))) =
      (T.map (fun z : ℂˣ => (z : ℂ))).map F := by
    rw [Multiset.map_map]; rfl
  have hc : ∀ M : Multiset ℂˣ, (do let a ← M; pure (a : ℂ) : Multiset ℂ) = M.map (fun z : ℂˣ => (z : ℂ)) :=
    fun M => Multiset.bind_singleton M _
  simp only [hc, Multiset.map_id'] at hT
  rw [h1, ← hT, GlobalTheory.multiset_map_prod_finset_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [GlobalTheory.multiset_map_prod_finset_sum]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl (fun z _ => ?_)
  simp only [Function.comp, hF]
  rw [Complex.cpow_add _ _ hq']
  ring_nf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParameterGLOfConjLinearIntertwiner
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LFun.SatConj

open ComplexConjugate

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) : (s.map (starRingEnd ℂ)).esymm j = conj (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun t _ => ?_
  simp [map_multiset_prod]

theorem conj_satEig (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    conj (GlobalTheory.LFun.satEig q n B j) = GlobalTheory.LFun.satEig q n (B.map star) j := by
  have hz : conj (((j : ℂ) * ((n : ℂ) - j)) / 2) = ((j : ℂ) * ((n : ℂ) - j)) / 2 := by
    rw [map_div₀, map_mul, map_sub, Complex.conj_natCast, Complex.conj_natCast, map_ofNat]
  have harg : (q : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_pos.ne
  have hp : conj ((q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
    have := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) harg
    rw [hz, Complex.conj_natCast] at this
    exact this.symm
  have hm : ((B.map star).map fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (starRingEnd ℂ) := by
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [Units.coe_star]
  rw [GlobalTheory.LFun.satEig, GlobalTheory.LFun.satEig, map_mul, hp, hm, esymm_map_conj]

theorem conj_Tj {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ) (g : GL (Fin n) L) :
    conj (Formalism.UG.Tj ℂ n O ϖ j g) = Formalism.UG.Tj ℂ n O ϖ j g := by
  classical
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply]
  split_ifs <;> simp

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
  {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}

theorem isSatVecGL_conj (J : V ≃ₗ⋆[ℂ] W) (hJ : ∀ g x, ρ' g (J x) = J (ρ g x)) {x : V} {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.IsSatVecGL w ρ x B) : GlobalTheory.LFun.IsSatVecGL w ρ' (J x) (B.map star) := by
  obtain ⟨h0, hfix, hcard, hT⟩ := h
  refine ⟨fun e => h0 (J.map_eq_zero_iff.1 e), GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [hJ, GlobalTheory.LGrp.mem_fixed.1 hfix k hk], by simp [hcard], fun ϖ hϖ j hj => ?_⟩
  have hfin := GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x
  have e1 : GlobalTheory.LFun.heckeVec ρ' (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) (J x) =
      J (GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) x) := by
    rw [GlobalTheory.LFun.heckeVec, GlobalTheory.LFun.heckeVec]
    refine (finsum_congr fun c => ?_).trans
      (AddMonoidHom.map_finsum (J.toLinearMap.toAddMonoidHom) hfin).symm
    simp [hJ, conj_Tj]
  rw [e1, hT ϖ hϖ j hj, LinearEquiv.map_smulₛₗ, conj_satEig]

end GlobalTheory.LFun.SatConj

open GlobalTheory.LFun.SatConj in

theorem GlobalTheory.LFun.hasSatGL_of_conjIntertwiner : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (J : V ≃ₗ⋆[ℂ] W), (∀ g x, ρ' g (J x) = J (ρ g x)) → ∀ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w ρ B → GlobalTheory.LFun.HasSatGL w ρ' (B.map star) := by
  intro E _ _ w n V W _ _ _ _ ρ ρ' J hJ B hB
  have hJs : ∀ g y, ρ g (J.symm y) = J.symm (ρ' g y) := fun g y => by
    apply J.injective
    rw [← hJ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := hB.exists_vec
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨J x, (isSatVecGL_conj J hJ hx).2.1, (isSatVecGL_conj J hJ hx).1⟩,
    fun y hy h0 => ?_⟩
  have hy' : J.symm y ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [hJs, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
  have := isSatVecGL_conj J hJ (hB.2 _ hy' fun e => h0 (by simpa using congrArg J e))
  rwa [LinearEquiv.apply_symm_apply] at this
end
end

