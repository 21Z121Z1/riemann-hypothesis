import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImagQuadIntegerLatticeMulStableISqrt
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IntLatMul

theorem main : ∀ (d : ℕ) (Λ : PeriodPair), 0 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    MulStable Λ (Complex.I * (Real.sqrt d : ℝ)) ∧ (Complex.I * (Real.sqrt d : ℝ)).im ≠ 0 := by
  intro d Λ hd hΛ
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwi : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast, hw2]
    ring
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxi, a, b, hab⟩ := (hΛ x).1 hx
    refine (hΛ _).2 ⟨hwi.mul hxi, -(b * d), a, ?_⟩
    rw [hab]
    push_cast
    linear_combination (b : ℂ) * hw2
  · have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    simp [hw, hs.ne']

end GlobalTheory.IntLatMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureEtaleAtOfHeightLeOnePurityStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosureEtaleAt_of_height_le_one_purity : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime], P.height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one) | (exact GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one) | (intros; apply GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.KS

namespace GlobalTheory.KS.Refine

local macro "opens_le" : tactic =>
  `(tactic| (rw [SetLike.le_def]; intro y hy; simp only [TopologicalSpace.Opens.mem_inf] at hy ⊢; aesop))

theorem isCob_of_refine : ∀ {Y : Scheme.{0}} {I J : Type} (Uc : I → Y.Opens) (c : GlobalTheory.KS.C1 Uc),
    GlobalTheory.KS.IsCoc Uc c → ∀ (V : J → Y.Opens) (σ : J → I), (∀ p, V p ≤ Uc (σ p)) → (⨆ p, V p = ⊤) →
    ∀ (B : ∀ p, Γ(Y, V p)), (∀ p p', GlobalTheory.KS.rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      GlobalTheory.KS.rsT (B p') (V p ⊓ V p') - GlobalTheory.KS.rsT (B p) (V p ⊓ V p')) → GlobalTheory.KS.IsCob Uc c := by
  intro Y I J Uc c hc V σ hV hVt B hB
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, O ⊓ V p := by
    intro O x hx
    have : x ∈ ⨆ p, V p := by rw [hVt]; trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    simp (disch := opens_le) only [rsT_rsT] at h1 h2 ⊢
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left) (cov _) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  simp (disch := opens_le) only [rsT_rsT] at h1 h2 h3 ⊢
  linear_combination h1 - h2 + h3

end GlobalTheory.KS.Refine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectivePreimageStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_surjective_to_colimit : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0}) [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected] (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G), (∀ x : X, ∃ U ∈ 𝒰, x ∈ G U) → ∀ (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U), (∀ U, IsClosedImmersion (e U)) → (∀ U, Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → ∀ j : X ⟶ colimit F, (∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U) → IsClosedImmersion j ∧ Surjective j ∧ ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
  first | exact @GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage | exact GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage | (intros; apply GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommMonObjOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem isCommMonObj_of_grpPullback : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsCommMonObj G' := by
  intro S S' G _ _ G' _ f φ h
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
  rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
    ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
section
noncomputable section

namespace GlobalTheory.FinGL.Transport

open Formalism.L2.DIV

theorem isIrreducible_comp {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) (f : G' →* G) (hf : Function.Surjective f) (h : σ.IsIrreducible) :
    Representation.IsIrreducible (σ.comp f : Representation ℂ G' V) := by
  let Φ : Subrepresentation (σ.comp f : Representation ℂ G' V) ≃o Subrepresentation σ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact U.apply_mem_toSubmodule g' hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact Φ.isSimpleOrder

theorem character_coind {G G' P P' V : Type} [Group G] [Group G'] [Group P] [Group P'] [AddCommGroup V] [Module ℂ V]
    (i : P →* G) (i' : P' →* G') (σ : Representation ℂ P V) (F : G' ≃* G) (f : P' →* P) (hf : Function.Surjective f)
    (hc : ∀ p, F (i' p) = i (f p)) (x : G') :
    (Representation.coind i' (σ.comp f : Representation ℂ P' V)).character x =
      (Representation.coind i σ).character (F x) := by
  let L : Representation.coindV i σ ≃ₗ[ℂ] Representation.coindV i' (σ.comp f : Representation ℂ P' V) :=
    { toFun := fun φ => ⟨fun y => φ.1 (F y), fun p y => by
        show φ.1 (F (i' p * y)) = σ (f p) (φ.1 (F y))
        rw [map_mul, hc]
        exact φ.2 _ _⟩
      invFun := fun φ => ⟨fun y => φ.1 (F.symm y), fun p y => by
        obtain ⟨p', rfl⟩ := hf p
        show φ.1 (F.symm (i (f p') * y)) = σ (f p') (φ.1 (F.symm y))
        rw [map_mul, ← hc, MulEquiv.symm_apply_apply]
        exact φ.2 _ _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun φ => Subtype.ext (funext fun y => congrArg φ.1 (F.apply_symm_apply y))
      right_inv := fun φ => Subtype.ext (funext fun y => congrArg φ.1 (F.symm_apply_apply y)) }
  unfold Representation.character
  rw [← LinearMap.trace_conj' _ L]
  congr 1
  refine LinearMap.ext fun φ => Subtype.ext (funext fun y => ?_)
  show φ.1 (y * x) = φ.1 (F.symm (F y * F x))
  rw [← map_mul, MulEquiv.symm_apply_apply]

variable {κ κ' : Type} [Field κ] [Field κ'] {r : ℕ}

def glEquiv (e : κ' ≃+* κ) (r : ℕ) : GL (Fin r) κ' ≃* GL (Fin r) κ :=
  { Matrix.GeneralLinearGroup.map (e : κ' →+* κ) with
    invFun := Matrix.GeneralLinearGroup.map (e.symm : κ →+* κ')
    left_inv := fun g => by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    right_inv := fun g => by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply] }

def triMap (e : κ' →+* κ) (b : Fin r → ℕ) : blockTri (κ := κ') b →* blockTri (κ := κ) b :=
  ((Matrix.GeneralLinearGroup.map e).comp (blockTri (κ := κ') b).subtype).codRestrict _ fun p i j hij => by
    have h : (p.1 : Matrix (Fin r) (Fin r) κ') i j = 0 := p.2 hij
    show e ((p.1 : Matrix (Fin r) (Fin r) κ') i j) = 0
    rw [h, map_zero]

theorem triMap_apply (e : κ' →+* κ) (b : Fin r → ℕ) (p : blockTri (κ := κ') b) (i j : Fin r) :
    ((triMap e b p : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      e (((p : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j) := rfl

theorem triMap_surjective (e : κ' ≃+* κ) (b : Fin r → ℕ) : Function.Surjective (triMap (e : κ' →+* κ) b) := fun p =>
  ⟨triMap (e.symm : κ →+* κ') b p, by
    ext i j
    simp [triMap_apply]⟩

theorem triMap_eq_one_iff (e : κ' →+* κ) (b : Fin r → ℕ) (p : blockTri (κ := κ') b) (i j : Fin r) :
    ((triMap e b p : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = (1 : Matrix (Fin r) (Fin r) κ) i j ↔
      ((p : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = (1 : Matrix (Fin r) (Fin r) κ') i j := by
  have h1 : (1 : Matrix (Fin r) (Fin r) κ) i j = e ((1 : Matrix (Fin r) (Fin r) κ') i j) := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [triMap_apply, h1, e.injective.eq_iff]

theorem isCuspDatum_comp {V : Type} [AddCommGroup V] [Module ℂ V] (e : κ' ≃+* κ) (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := κ) b) V) (h : IsCuspDatum b σ) :
    IsCuspDatum b (σ.comp (triMap (e : κ' →+* κ) b) : Representation ℂ (blockTri (κ := κ') b) V) where
  mono := h.mono
  irr := isIrreducible_comp σ _ (triMap_surjective e b) h.irr
  infl := fun p hp => h.infl _ fun i j hij => (triMap_eq_one_iff _ b p i j).2 (hp i j hij)
  cusp := fun S hS y hy => h.cusp S hS y fun u hu => by
    obtain ⟨u', rfl⟩ := triMap_surjective e b u
    exact hy u' fun i j hij => hu i j fun h' => hij ((triMap_eq_one_iff _ b u' i j).1 h')

theorem isCuspProdChar_transport : ∀ (κ κ' : Type) [Field κ] [Field κ'] (e : κ ≃+* κ') (r : ℕ) (θ : GL (Fin r) κ → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar
      (fun x : GL (Fin r) κ' => θ (Matrix.GeneralLinearGroup.map (e.symm : κ' →+* κ) x)) := by
  rintro κ κ' _ _ e r θ ⟨d, b, σ, hσ, hθ⟩
  refine ⟨d, b, σ.comp (triMap (e.symm : κ' →+* κ) b), isCuspDatum_comp e.symm b σ hσ, fun x => ?_⟩
  show θ _ = _
  rw [hθ]
  exact (character_coind _ _ σ (glEquiv e.symm r) _ (triMap_surjective e.symm b) (fun _ => rfl) x).symm

end GlobalTheory.FinGL.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfIsProperOfFormallyUnramified
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.PropFin

theorem isFinite_of_isProper_of_formallyUnramified :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [IsLocallyNoetherian S],
      IsProper f → FormallyUnramified f → IsFinite f := by
  intro X S f _ hp hu
  have hlqf : LocallyQuasiFinite f := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := f.formallyUnramified_appLE hU hV e
    have h₂ := f.finiteType_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end GlobalTheory.PropFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdeleTranslateIntegralAdditiveTotalProperties
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpFam.TrAdd

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem tr_iff {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (x x' : K) :
    Tr t x x' ↔ (t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x ∈
      adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [mem_adelicIdeal_one_iff]; rfl

theorem main : ∀ (K : Type) [Field K] [NumberField K] (t : (Af K)ˣ), (∀ x x' y y' : K, Tr t x x' → Tr t y y' → Tr t (x - y) (x' - y')) ∧ (∀ (a x x' : K), IsIntegral ℤ a → Tr t x x' → Tr t (a * x) (a * x')) ∧ (∀ x : K, ∃ x', Tr t x x') ∧ (∀ x' : K, ∃ x, Tr t x x') := by
  intro K _ _ t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy
    rw [tr_iff] at *
    have := sub_mem hx hy
    convert this using 1
    simp only [map_sub]
    ring
  · intro a x x' ha hx
    rw [tr_iff] at *
    let b : 𝓞 K := ⟨a, ha⟩
    have := Submodule.smul_mem _ b hx
    convert this using 1
    ext v
    rw [adele_smul_apply]
    have : algebraMap (𝓞 K) K b = a := rfl
    rw [this]
    simp only [adele_sub_apply, adele_mul_apply, adele_algebraMap_apply, map_mul]
    ring
  · intro x
    have hI : ((t⁻¹ : (Af K)ˣ) • (1 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 :=
      GlobalTheory.Idele.smul_ne_zero _ one_ne_zero
    obtain ⟨x', hx'⟩ := exists_sub_mem_adelicIdeal hI (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x)
    refine ⟨x', ?_⟩
    rw [tr_iff]
    have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
        ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
      rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
      ring
    rw [e, mul_mem_adelicIdeal_smul] at hx'
    simpa using neg_mem hx'
  · intro x'
    obtain ⟨x, hx⟩ := exists_sub_mem_adelicIdeal (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))
      ((t : Af K) * algebraMap K (Af K) x')
    exact ⟨x, (tr_iff t x x').2 hx⟩

end GlobalTheory.WpFam.TrAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplicationStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 → IsIntegral ℤ (jT τ) := by
  first | exact @GlobalTheory.JInt.main | exact GlobalTheory.JInt.main | (intros; apply GlobalTheory.JInt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAwayFibStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalization_away_ferrandPush_fib : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂], ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U), letI := ((GlobalTheory.FerrandPush.fib i₁ i₂).map (homOfLE (Y₀.basicOpen_le (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a ((GlobalTheory.FerrandPush.fib i₁ i₂).obj (op (Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a)))) := by
  first | exact @GlobalTheory.FerrandPush.isLocalization_away_fib | exact GlobalTheory.FerrandPush.isLocalization_away_fib | (intros; apply GlobalTheory.FerrandPush.isLocalization_away_fib; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyDirectedOfBasisStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyDirected_of_bijective_basis_compatible : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : B₀, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → ∀ (F : 𝒰 ⥤ Scheme.{0}), (∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)) → ∀ (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U), (∀ U, Function.Injective (e U)) → (∀ U, Function.Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → (F ⋙ Scheme.forget).IsLocallyDirected := by
  first | exact @GlobalTheory.ThickGlue.isLocallyDirected_of_basis | exact GlobalTheory.ThickGlue.isLocallyDirected_of_basis | (intros; apply GlobalTheory.ThickGlue.isLocallyDirected_of_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

def QHyp {S : Scheme.{0}} (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left)

def formLB {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) {G : Over S} {r : ℕ} (pr : Fin r → (G ⟶ A))
    (W : Matrix (Fin r) (Fin r) ℤ) : LB G.left :=
  LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)

def diagPow {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) (d : ℤ) : LB A.left :=
  LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => d)

def sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : (G' ⊗ G').left ⟶ (G ⊗ G).left :=
  pullback.lift ((fst G' G').left ≫ φ) ((snd G' G').left ≫ φ) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, Over.w (fst G' G'), Over.w (snd G' G')])

theorem isSquare_sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : IsSquare φ (sqMap f φ w) :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {φ' : G''.left ⟶ G'.left} {φ₂' : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare φ' φ₂') (h : IsSquare φ φ₂) : IsSquare (φ' ≫ φ) (φ₂' ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
   by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isMonHom_prodPow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (c : Fin r → ℤ) : IsMonHom (∏ k, f k ^ c k) :=
  Finset.prod_induction _ (fun x => IsMonHom x) (fun a b ha hb => by
    haveI := ha; haveI := hb; exact GlobalTheory.Serre.isMonHom_mul a b) GlobalTheory.Serre.isMonHom_one fun k _ => by
    haveI := hf k; exact GlobalTheory.Serre.isMonHom_zpow _ _

theorem powext {S : Scheme.{0}} (A : Over S) (r : ℕ) {X : Scheme.{0}} (a b : X ⟶ (Out.powObj A r).left)
    (h0 : a ≫ (Out.powObj A r).hom = b ≫ (Out.powObj A r).hom)
    (h : ∀ k, a ≫ (Out.powPr A k).left = b ≫ (Out.powPr A k).left) : a = b := by
  have := (Out.powIsLimit A r).hom_ext (W := Over.mk (b ≫ (Out.powObj A r).hom)) (f := Over.homMk a h0)
    (f' := Over.homMk b rfl) (fun ⟨k⟩ => Over.OverMorphism.ext (by simpa using h k))
  exact congrArg (fun m => m.left) this

end GlobalTheory.ActFin
end
end

