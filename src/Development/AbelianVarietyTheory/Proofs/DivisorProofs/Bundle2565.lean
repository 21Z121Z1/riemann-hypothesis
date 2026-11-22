import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appTop_bijective_and_surjective_normalDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  first | exact @GlobalTheory.Mum.Modif.appTop_bijective_surjective | exact GlobalTheory.Mum.Modif.appTop_bijective_surjective | (intros; apply GlobalTheory.Mum.Modif.appTop_bijective_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopInjectiveOfSurjectiveIntegralToSpecDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appTop_injective_of_surjective_integral_toSpecDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π → IsIntegral S → Function.Injective π.appTop.hom := by
  first | exact @GlobalTheory.appTop_injective_of_surjective_toSpec_domain | exact GlobalTheory.appTop_injective_of_surjective_toSpec_domain | (intros; apply GlobalTheory.appTop_injective_of_surjective_toSpec_domain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLatticeStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbertFactor_imForm_integral_on_lattice : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  first | exact @GlobalTheory.TorusRM.ahFactor_im_int | exact GlobalTheory.TorusRM.ahFactor_im_int | (intros; apply GlobalTheory.TorusRM.ahFactor_im_int <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleHermPos

open Complex Matrix
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues AnalyticHom

variable {g : ℕ}

lemma form_smul (c : ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    z ⬝ᵥ ((c : ℂ) • Hm).mulVec (star w) = c * (z ⬝ᵥ Hm.mulVec (star w)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma isHermitian_smul {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (c : ℝ) :
    ((c : ℂ) • Hm).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]

lemma theta_add_smul_eq (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (htr : ∀ (l : Λ) z, θ (z + l) =
      (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z)
    {v : Fin g → ℂ} (hv : Hm.mulVec (star v) = 0) (z : Fin g → ℂ) (t : ℂ) :
    θ (z + t • v) = θ z := by
  obtain ⟨C, hC⟩ := ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr
  have hq : ∀ t : ℂ, ((z + t • v) ⬝ᵥ Hm.mulVec (star (z + t • v))) = z ⬝ᵥ Hm.mulVec (star z) := by
    intro t
    have h1 : Hm.mulVec (star (t • v)) = 0 := by rw [star_smul, mulVec_smul, hv, smul_zero]
    have h2 : v ⬝ᵥ Hm.mulVec (star z) = 0 := by
      rw [ThetaPositivity.form_conj hH z v, hv, dotProduct_zero, star_zero]
    rw [star_add, mulVec_add, h1, add_zero, add_dotProduct, smul_dotProduct, h2, smul_zero, add_zero]
  have hd : Differentiable ℂ fun t : ℂ => θ (z + t • v) :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const v))
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => θ (z + t • v)) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re), ?_⟩
    rintro _ ⟨t, rfl⟩
    have := hC (z + t • v)
    rwa [hq t] at this
  have := hd.apply_eq_apply_of_bounded hb t 0
  simpa using this

lemma eq_zero_of_smul_mem (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] {v : Fin g → ℂ}
    (h : ∀ t : ℂ, t • v ∈ Λ) : v = 0 := by
  have hc : Continuous fun t : ℂ => (⟨t • v, h t⟩ : Λ) :=
    (continuous_id.smul continuous_const).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val this

theorem re_form_pos_of_relAmple :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB →
    Out.RelAmple A L → ∀ (g : ℕ) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) →
      (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
        u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)) →
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro A _ _ hA L hL ha g u Hm χ hH hχ hfr
  haveI : Smooth A.hom := hA.smooth
  haveI := isReduced_of_smooth_complex _ A.hom inferInstance
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  obtain ⟨N, hN, M, s, hcov, hD⟩ := ha ⊤ (isAffineOpen_top _)
  choose hDa r hr hsurj using hD
  have hrg : Set.range (𝟙 A.left : A.left ⟶ A.left) ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    trivial
  obtain ⟨σ, hσ⟩ : ∃ σ : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, σ ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrg⟩
  choose s' hs' using fun i => exists_sec_pow L _ σ hσ N A.hom (s i)
  choose θ hθd hθfn _hθu hθper using fun i => ThetaBundleSec.exists_fn u hL N (s' i)
  choose ch hch using fun z => PullHermitian.exists_chart (u.ex z).left hL
  have hU : ∀ z, ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ (Out.powOver A L ⊤ N).U (fun _ => ch z) := fun z =>
    le_preimage_mono (u.ex z).left (chart_le L _ σ hσ N fun _ => ch z)
      ((le_preimage_lbPow _ L N fun _ => ch z).2 (hch z))
  have hval : ∀ i z, valAt' ((u.ex z).left ≫ σ) ((Out.powOver A L ⊤ N).U fun _ => ch z)
      ((s i).f fun _ => ch z) = θ i z * u.fr (ch z) z ^ N := fun i z =>
    have k := (le_preimage_lbPow _ L N fun _ => ch z).2 (hch z)
    (hs' i _ _ k).symm.trans (hθfn i _ z k)
  have hfr0 : ∀ z, u.fr (ch z) z ^ N ≠ 0 := fun z => pow_ne_zero _ (u.fr_ne _ _ (hch z))
  have hmem : ∀ i z, ⊤ ≤ ((u.ex z).left ≫ σ) ⁻¹ᵁ Out.nonzeroLocus (s i) ↔ θ i z ≠ 0 := fun i z => by
    rw [le_preimage_nonzeroLocus _ (s i) _ (hU z), hval, mul_ne_zero_iff_right (hfr0 z)]
  have hcov' : ∀ z, ∃ i, θ i z ≠ 0 := fun z => by
    have hz : ((u.ex z).left ≫ σ) (default : PrimeSpectrum ℂ) ∈ ⨆ i, Out.nonzeroLocus (s i) := by
      rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact ⟨i, (hmem i z).1 ((top_le_preimage_iff_mem _ _).2 hi)⟩

  set HN : Matrix (Fin g) (Fin g) ℂ := ((N : ℝ) : ℂ) • Hm with hHNdef
  have hHN : HN.IsHermitian := isHermitian_smul hH _
  have htr : ∀ i (l : u.Λ) z, θ i (z + l) =
      (χ l ^ N * cexp (Real.pi * (z ⬝ᵥ HN.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HN.mulVec (star (l : Fin g → ℂ))))) * θ i z := by
    intro i l z
    have hper : u.ex (z + l) = u.ex z := by rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
    rw [hθper i z (z + l) _ hper fun j hj => hfr l j z hj, form_smul, form_smul, mul_pow,
      ← Complex.exp_nat_mul]
    congr 3
    push_cast
    ring
  have hχN : ∀ l, ‖χ l ^ N‖ = 1 := fun l => by rw [norm_pow, hχ, one_pow]

  obtain ⟨i0, hi0⟩ := hcov' 0
  have hne : θ i0 ≠ 0 := fun h => hi0 (by rw [h]; rfl)
  obtain ⟨C, hC⟩ := ThetaPositivity.exists_norm_le u.Λ hHN (fun l => χ l ^ N) hχN
    (hθd i0).continuous (htr i0)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnn : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := fun w => by
    by_contra hw
    push_neg at hw
    have hw' : (w ⬝ᵥ HN.mulVec (star w)).re < 0 := by
      rw [form_smul, re_ofReal_mul]
      exact mul_neg_of_pos_of_neg hNpos hw
    exact hne (ThetaPositivity.eq_zero_of_neg hHN (hθd i0) hC hw')

  have hrval : ∀ i j w, θ i w ≠ 0 →
      valAt' ((u.ex w).left ≫ σ) (Out.nonzeroLocus (s i)) (r i j) * θ i w = θ j w := by
    intro i j w hw
    have hw' := (hmem i w).2 hw
    have k := (le_preimage_inf _ _ _).2 ⟨hw', hU w⟩
    have k₁ := congrArg (valAt' ((u.ex w).left ≫ σ) _) (hr i j fun _ => ch w)
    rw [val_mul _ k, val_resG _ _ k, val_resG _ _ k, val_resG _ _ k, hval, hval,
      ← _root_.mul_assoc] at k₁
    exact (mul_right_cancel₀ (hfr0 w) k₁).symm
  have hc : ∀ w w', ((u.ex w).left ≫ σ) ≫ (A.hom ∣_ ⊤) = ((u.ex w').left ≫ σ) ≫ (A.hom ∣_ ⊤) := by
    intro w w'
    rw [← cancel_mono (⊤ : (Sp ℂ).Opens).ι]
    simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hσ, Over.w]

  have hker : ∀ v : Fin g → ℂ, Hm.mulVec (star v) = 0 → v = 0 := by
    intro v hv
    have hvN : HN.mulVec (star v) = 0 := by rw [hHNdef, Matrix.smul_mulVec, hv, smul_zero]
    have hinv : ∀ i (t : ℂ), θ i (t • v) = θ i 0 := fun i t => by
      simpa using theta_add_smul_eq u.Λ hHN _ hχN (hθd i) (htr i) hvN 0 t
    have hpt : ∀ t : ℂ, (u.ex (t • v)).left ≫ σ = (u.ex 0).left ≫ σ := by
      intro t
      obtain ⟨i, h0⟩ := hcov' 0
      have h0' : θ i (t • v) ≠ 0 := by rw [hinv]; exact h0
      have m0 := (hmem i 0).2 h0
      have mt := (hmem i _).2 h0'
      refine UnifTangent.eq_of_values (hDa i) mt m0 fun f => ?_
      obtain ⟨Q, rfl⟩ := hsurj i f
      induction Q using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.eval₂Hom_C]
        exact (val_appLE _ (A.hom ∣_ ⊤) ⊤ _ _ a mt).trans
          ((congrArg (fun y => valAt' y ⊤ a) (hc _ 0)).trans (val_appLE _ (A.hom ∣_ ⊤) ⊤ _ _ a m0).symm)
      | add Q Q' h h' => rw [map_add, val_add _ mt, val_add _ m0, h, h']
      | mul_X Q j h =>
        rw [map_mul, val_mul _ mt, val_mul _ m0, h, MvPolynomial.eval₂Hom_X']
        congr 1
        have a1 := hrval i j _ h0'
        have a2 := hrval i j 0 h0
        rw [hinv, hinv] at a1
        exact mul_right_cancel₀ h0 (a1.trans a2.symm)
    refine eq_zero_of_smul_mem u.Λ fun t => (u.ker _).1 ?_
    have e : u.ex (t • v) = u.ex 0 := by
      ext1
      have := hpt t =≫ (A.hom ⁻¹ᵁ ⊤).ι
      rwa [Category.assoc, Category.assoc, hσ, Category.comp_id, Category.comp_id] at this
    have e0 : u.ex 0 = 1 := by
      have h00 := u.ex_add 0 0
      rw [add_zero] at h00
      exact (mul_eq_left.mp h00.symm)
    rw [e, e0]

  intro z hz
  have him : ∀ w : Fin g → ℂ, (w ⬝ᵥ Hm.mulVec (star w)).im = 0 := fun w => by
    have h := congrArg Complex.im (ThetaPositivity.form_conj hH w w)
    simp only [star_def, conj_im] at h
    linarith
  refine lt_of_le_of_ne (hnn z) fun h0 => hz (hker z ?_)
  open scoped ComplexOrder in
  have hpsd : Hm.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun x => ?_⟩
    have h1 := hnn (star x)
    have h2 := him (star x)
    rw [star_star] at h1 h2
    exact Complex.le_def.mpr ⟨h1, h2.symm⟩
  refine (hpsd.dotProduct_mulVec_zero_iff (star z)).mp ?_
  rw [star_star]
  exact Complex.ext h0.symm (him z)

end GlobalTheory.AmpleHermPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertForm.FormEx

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem arFun_eq_rename (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) {ι κ : Type} [Fintype ι] [Fintype κ]
    {L : ι → HermLB p} {M : κ → HermLB p} {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} {Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun L D Φ) (hΨ : IsArFun M D Ψ) (r : ι → κ) (hr : ∀ i, M (r i) = L i) :
    Φ = Ψ ∘ₗ (MvPolynomial.rename r : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial κ ℝ).toLinearMap := by
  have h := ((H.arIso k X p D hX).2 κ M Ψ hΨ).2.2 ι L (fun i => Pi.single (r i) 1) (fun i => by
    rw [← hr i]; exact isometric_comb_single M (r i))
  rw [Model.isArFun_unique hX hΦ h]
  congr 2
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [MvPolynomial.aeval_X, lin_single, MvPolynomial.rename_X]

def famFn (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) {n : ℕ} (f : Fin n → HermLB p) : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ :=
  Classical.choose (((H.arExists k X p D hX).2 (Fin n) f).1)

theorem famFn_spec (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) {n : ℕ} (f : Fin n → HermLB p) :
    IsArFun f D (famFn H hX f) :=
  Classical.choose_spec (((H.arExists k X p D hX).2 (Fin n) f).1)

def enum (S : Finset (HermLB p)) (i : Fin S.card) : HermLB p := (S.equivFin.symm i).1

theorem enum_injective (S : Finset (HermLB p)) : Function.Injective (enum S) :=
  fun _ _ h => S.equivFin.symm.injective (Subtype.ext h)

theorem enum_equivFin (S : Finset (HermLB p)) {x : HermLB p} (hx : x ∈ S) : enum S (S.equivFin ⟨x, hx⟩) = x := by
  simp [enum]

theorem range_enum (S : Finset (HermLB p)) : Set.range (enum S) = S :=
  Set.ext fun x => ⟨by rintro ⟨i, rfl⟩; exact (S.equivFin.symm i).2, fun hx => ⟨_, enum_equivFin S hx⟩⟩

def total (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) : MvPolynomial (HermLB p) ℝ →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials (HermLB p) ℝ).constr ℝ fun m =>
    famFn H hX (enum m.support) (MvPolynomial.monomial (m.comapDomain (enum m.support) (enum_injective _).injOn) 1)

theorem total_rename (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) {ι : Type} [Fintype ι] (L : ι → HermLB p)
    {Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun L D Φ) :
    total H hX ∘ₗ (MvPolynomial.rename L : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial (HermLB p) ℝ).toLinearMap = Φ := by
  refine (MvPolynomial.basisMonomials ι ℝ).ext fun m => ?_
  rw [MvPolynomial.coe_basisMonomials, LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.rename_monomial,
    total, ← congrFun (MvPolynomial.coe_basisMonomials (HermLB p) ℝ) (Finsupp.mapDomain L m), Module.Basis.constr_basis]
  set n := Finsupp.mapDomain L m
  let T : Finset (HermLB p) := Finset.univ.image L
  have hL (i : ι) : L i ∈ T := Finset.mem_image_of_mem L (Finset.mem_univ i)
  have hST : n.support ⊆ T := fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact hL i
  have hS (i : Fin n.support.card) : enum n.support i ∈ T := hST (by rw [← Finset.mem_coe, ← range_enum]; exact ⟨i, rfl⟩)
  have k1 := arFun_eq_rename H hX hΦ (famFn_spec H hX (enum T)) (fun i => T.equivFin ⟨L i, hL i⟩)
    fun i => enum_equivFin T (hL i)
  have k2 := arFun_eq_rename H hX (famFn_spec H hX (enum n.support)) (famFn_spec H hX (enum T))
    (fun i => T.equivFin ⟨_, hS i⟩) fun i => enum_equivFin T (hS i)
  rw [k1, k2, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.rename_monomial, MvPolynomial.rename_monomial]
  congr 3
  refine Finsupp.mapDomain_injective (M := ℕ) (enum_injective T) ?_
  rw [← Finsupp.mapDomain_comp (M := ℕ), ← Finsupp.mapDomain_comp (M := ℕ)]
  have e1 : enum T ∘ (fun i => T.equivFin ⟨_, hS i⟩) = enum n.support := funext fun i => enum_equivFin T (hS i)
  have e2 : enum T ∘ (fun i => T.equivFin ⟨L i, hL i⟩) = L := funext fun i => enum_equivFin T (hL i)
  rw [e1, e2, Finsupp.mapDomain_comapDomain _ (enum_injective _) _ (by rw [range_enum])]

def linOf : Cl p →ₗ[ℝ] MvPolynomial (HermLB p) ℝ := Finsupp.linearCombination ℝ fun L => MvPolynomial.X L

def num (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) : Form (Cl p) D :=
  (total H hX).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra ℝ (Fin (D + 1)) (MvPolynomial (HermLB p) ℝ)).compLinearMap fun _ => linOf)

theorem num_apply (H : GlobalTheory.Published.ArCalc) (hX : IsArithVar p D) (v : Fin (D + 1) → Cl p) :
    num H hX v = total H hX (∏ j, linOf (v j)) := by
  simp [num]

end GlobalTheory.VertForm.FormEx

namespace GlobalTheory.VertForm

theorem exists_symm_arForm : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ num : Form (Cl p) D, IsArForm D num ∧ IsSymm num := by
  intro H k _ X _ p D hX
  refine ⟨FormEx.num H hX, fun ι _ L Φ hΦ a => ?_, fun v π => ?_⟩
  · rw [FormEx.num_apply, ← FormEx.total_rename H hX L hΦ, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [lin, FormEx.linOf, map_sum, cl, Finsupp.linearCombination_single, MvPolynomial.smul_eq_C_mul]
  · rw [FormEx.num_apply, FormEx.num_apply]
    congr 1
    exact Equiv.prod_comp π fun j => FormEx.linOf (v j)

end GlobalTheory.VertForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyRelativeDimDrop
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory

theorem dim_ne_zero_of_isProjOver {k : Type} [CommRing k] {Z : Scheme.{0}} (q : Z ⟶ Sp k)
    [IsIntegral Z] (hq : IsProjOver q) (hfin : Module.Finite ℤ k) (hc : CharZero Γ(Z, ⊤)) :
    topologicalKrullDim Z ≠ 0 := fun h0 => by
  obtain ⟨N, j, _, hj⟩ := hq
  have := isProper_str k N
  have : IsProper q := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hfin)
  let t := q ≫ spMap (Int.castRingHom k)
  have : Flat t := (flat_int_iff_charZero t).2 hc
  obtain ⟨z, -, hz⟩ := Flat.generalizingMap t (genericPoint_specializes (t (genericPoint Z)))
  have hs : Set.range t = Set.univ := by
    rw [← t.isClosedMap.isClosed_range.closure_eq]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec (Sp ℤ)).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ⟨z, hz⟩)))
  have hu (w : Z) : w = genericPoint Z := by
    have := Order.krullDim_nonpos_iff_forall_isMax.1 (show Order.krullDim (TopologicalSpace.IrreducibleCloseds Z) ≤ 0
      from h0.le) ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec Z)
  have hs' := Set.range_eq_univ.1 hs
  obtain ⟨a, ha⟩ := hs' (⊥ : PrimeSpectrum ℤ)
  obtain ⟨b, hb⟩ := hs' (⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2
    Int.prime_two⟩ : PrimeSpectrum ℤ)
  have e := congrArg PrimeSpectrum.asIdeal (hb.symm.trans (((hu b).trans (hu a).symm) ▸ ha))
  exact two_ne_zero (Ideal.span_singleton_eq_bot.1 e)

theorem isArithVar_of_surjective_dim_succ : ∀ (k : Type) [CommRing k] (Y Y₁ : Scheme.{0}) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k) (ρ : Y ⟶ Y₁) (D : ℕ),
    ρ ≫ q₁ = p → IsArithVar p D → IsIntegral Y₁ → IsProjOver q₁ → Surjective ρ →
    topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 → ∃ d₁ : ℕ, D = d₁ + 1 ∧ IsArithVar q₁ d₁ := by
  intro k _ Y Y₁ p q₁ ρ D hρ hX hI hP _ hd
  have hcY : CharZero Γ(Y, ⊤) := hX.charZero
  have hc : CharZero Γ(Y₁, ⊤) := (ρ.appTop).hom.charZero
  have hdim : topologicalKrullDim Y₁ = (D : ℕ) := by
    rw [hX.dim_eq] at hd
    generalize topologicalKrullDim Y₁ = a at hd ⊢
    induction a with
    | bot => exact absurd hd (by simp)
    | coe a =>
      induction a with
      | top =>
        exfalso
        have e1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
        rw [e1] at hd
        first
          | exact ENat.coe_ne_top _ (WithBot.coe_inj.1 hd)
          | exact ENat.coe_ne_top (D + 1) (WithBot.coe_inj.1 hd)
          | (simp at hd; exact WithBot.natCast_ne_top D hd)
          | (simp at hd; exact absurd hd (by simp [WithBot.none_eq_bot]))
      | coe a =>
        congr 2
        have := hd
        norm_cast at this
        omega
  have hD : D ≠ 0 := by
    rintro rfl
    exact dim_ne_zero_of_isProjOver q₁ hP hX.finite hc (by simpa using hdim)
  refine ⟨D - 1, by omega, hX.isDomain, hX.finite, hI, hP, (flat_int_iff_charZero _).2 hc, ?_⟩
  rw [hdim]
  congr 2
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.EigWhole

variable {D : D7} (O : Setup D)

abbrev Var : Type := DV.Rt D.what₂.Tau O.N ⊕ (Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))

def fam (T : Finset ℕ) (R : ℝ) : Var O → Sym D.host.E →₀ ℤ
  | .inl x => rootSym O.S.Dw (ArIn.ind T) (some R) (DV.tauEmb D x.1) x.2
  | .inr l => wholeSym (ArIn.ind T) (some R) l

def diffPol : MvPolynomial (Var O) ℝ :=
  (C (1 / 2 : ℝ) * ∑ l, X (Sum.inr l) ^ 2 - ∑ x, X (Sum.inl x) ^ 2) *
    rename Sum.inl (curveCl D.what₂.Tau O.N O.j)

def AwayAgree (T : Finset ℕ) (R : ℝ) (c : O.s.Comp) : Prop :=
  ∀ (k : ℕ) (z : Letter O.S.Dw), (letters O.S.Dw)[k]? = some z →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : GlobalTheory.TrueGeo.Ext v) (y : GlobalTheory.TrueGeo.AlgPt (O.var c)),
      ¬ resP v ∣ (NumberField.discr D.host.E).natAbs →
      lgOf (O.Φ.C c) (Finsupp.single (ArIn.ind T, some R, .inr k) 1) v ε y =
        lgOf (O.Φ.C c) (Finsupp.single (ArIn.ind T, some R, .inl (z.1, (z.2 : ℕ))) 1) v ε y

end GlobalTheory.EigWhole

namespace GlobalTheory.EigWhole

def RamModel : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
    AwayAgree O (Pad.setB O.κ B) R c →
    ∀ (M : GlobalTheory.TrueGeo.Model (O.var c)) (L : Var O → GlobalTheory.HermLB M.p) (m : ℕ+)
      (Ψ : MvPolynomial (Var O) ℝ →ₗ[ℝ] ℝ),
      (∀ i, (adlOf (O.Φ.C c) (O.met.hm c) (fam O (Pad.setB O.κ B) R i)).Induced M (L i) m 0) →
      (haveI := M.ar.isIntegral; GlobalTheory.ArInt.IsArFun L (O.var c).dim Ψ) →
      Ψ (diffPol O) = 0

end GlobalTheory.EigWhole

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeBisStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeBis : ∀ (S : Scheme.{0}) (A S' S'' : Over S) [GrpObj A] (g : ℕ) (_ : S'' ⟶ S'), HasRep A g S' → HasRep A g S'' := by
  first | exact @GlobalTheory.DualCon.HasRep.baseChange | exact GlobalTheory.DualCon.HasRep.baseChange | (intros; apply GlobalTheory.DualCon.HasRep.baseChange <;> assumption)
end

