import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0689

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DefectHom

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_zero (D : DegPre R) : D.c 0 = 1 := by
  have h : D.c (0 + 0) = D.c 0 * D.c 0 := D.c_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem c_neg (D : DegPre R) (a : D.X) : D.c (-a) = (D.c a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h : D.c (-a + a) = D.c (-a) * D.c a := D.c_add _ _
  rw [neg_add_cancel, c_zero] at h
  exact h.symm

theorem pt_neg (D : DegPre R) (a : D.X) : toUnit (TK R) ≫ D.c (-a) = (toUnit (TK R) ≫ D.c a)⁻¹ := by
  rw [c_neg, GrpObj.comp_inv]

theorem pt_add (D : DegPre R) (a b : D.X) :
    toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
  rw [D.c_add, ← MonObj.comp_mul]; rfl

theorem neg_pt_left (D : DegPre R) (a : D.X) : ptK (D.c (-a)) = D.xK a ≫ (ι[D.P.A]).left := by
  show (toUnit (TK R) ≫ D.c (-a)).left = _
  rw [pt_neg, Hom.inv_def, Over.comp_left]

theorem exists_defect (D : DegPre R) (χ : D.X) : ∃ k : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val (D.psi χ) (𝟙 _) z J := by
  let t := LB.mulGen D.P.L _ _ _ _ (D.psi (-χ)) (LB.pullGen D.P.L _ _ D.sym (D.xK χ))
  have ht : t.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)
  have hf : FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (-χ))) (fun k => D.xK χ ≫ ![(ι[D.P.A]).left, 𝟙 D.P.A.left] k))
      (Sum.elim (fun _ => -1) ![1, -1]) (fun _ : PUnit => ptK (D.c χ)) (fun _ => -1) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, neg_pt_left]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]
    simp only [zpow_neg, zpow_one]
    group
  obtain ⟨c, hc, H⟩ := DVR.TWM.exists_ratio (F := FractionRing R) D.P.isLB t ht (D.psi χ) (D.psi_gen χ) hf
  refine ⟨Units.mk0 c hc, fun z J hJ => ?_⟩
  have e := H _ (𝟙 _) z J hJ
  have e₁ : val t (𝟙 _) z J = val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J := by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
    rw [Category.id_comp]
  rw [← e₁]
  refine Units.ext (e.trans ?_)
  rw [Units.val_mul, ← gs_unit _ z ⊤ trivial]
  rfl

theorem gm_unitOn_inj {u v : (FractionRing R)ˣ} (z : (TK R).left)
    (h : gm (𝟙 (TK R).left) z ⊤ (unitOn u) = gm (𝟙 (TK R).left) z ⊤ (unitOn v)) : u = v := by
  have hs : Subsingleton (TK R).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing R)))
  have e : unitOn u = unitOn v := unit_ext fun x _ => by rw [Subsingleton.elim x z]; exact h
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1 e

theorem val_tau (D : DegPre R) (a b : D.X) {z : (TK R).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau a b) (𝟙 _) z J = val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ *
      (val (D.psi b) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem exists_evenDefect_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R),
    D.TauBimult → ∃ h : D.X → (FractionRing R)ˣ, (∀ a b, h (a + b) = h a * h b) ∧ EvenDefect D h := by
  intro R _ _ _ D hB
  choose h hh using exists_defect D
  refine ⟨h, fun a b => ?_, hh⟩
  let z : (TK R).left := (⊥ : PrimeSpectrum (FractionRing R))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  refine gm_unitOn_inj z ?_
  have g1 := GlobalTheory.T.symmetry_secondDifference_eq_cubical_ratio R D (TK R) (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) z J hJ
  have g2 := GlobalTheory.T.tau_period_val_neg_cubical_ratio R D hB a b z J hJ
  rw [← pt_neg, ← pt_neg, ← pt_add] at g1
  rw [val_tau D a b hJ, val_tau D (-a) (-b) hJ, ← neg_add] at g2
  have e₀ := hh (a + b) z J hJ
  have e₁ := hh a z J hJ
  have e₂ := hh b z J hJ
  change val D.sym (D.xK (a + b)) z J * _ = val D.sym (D.xK a) z J * val D.sym (D.xK b) z J * _ at g1
  rw [show unitOn (h a * h b) = unitOn (h a) * unitOn (h b) from map_mul _ _ _, map_mul]
  generalize val D.sym (D.xK (a + b)) z J = s₀ at g1 e₀
  generalize val D.sym (D.xK a) z J = s₁ at g1 e₁
  generalize val D.sym (D.xK b) z J = s₂ at g1 e₂
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h (a + b))) = k₀ at e₀ ⊢
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h a)) = k₁ at e₁ ⊢
  generalize gm (𝟙 (TK R).left) z ⊤ (unitOn (h b)) = k₂ at e₂ ⊢
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₀ := E e₀; have a₁ := E e₁; have a₂ := E e₂; have b₁ := E g1; have b₂ := E g2
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ b₁ b₂ ⊢
  linear_combination (norm := abel) -a₀ + a₁ + a₂ + b₁ - b₂
end GlobalTheory.DefectHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHost
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_host : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E), Nonempty (Host E) :=
  ⟨GlobalTheory.HostModel.E21, inferInstance, inferInstance, inferInstance, ⟨GlobalTheory.HostModel.host⟩⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftFormallySmoothSquareZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem idemLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B'] (e₀ : B₀' →ₐ[R₀] B₀'), (∀ x, e₀ (e₀ x) = e₀ x) → ∃ e : B' →ₐ[R] B', (∀ b, e (e b) = e b) ∧ ∀ b, p' (e b) = e₀ (p' b) := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ e₀ he₀
  obtain ⟨e, he⟩ := homLift R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' B' B₀' p' hs' hp' hker' e₀
  set J : Ideal B' := I.map (algebraMap R B') with hJ
  have hJ2 : ∀ x ∈ J, ∀ y ∈ J, x * y = 0 := by
    intro x hx y hy
    have : x * y ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [hJ, ← Ideal.map_pow, hI] at this
    simpa using this
  have hu : ∀ c, e (e c) - e c ∈ J := by
    intro c
    rw [← hker']
    simp [map_sub, he, he₀]
  have hkill : ∀ x ∈ J, ∀ c, e (e (c * x)) - e (c * x) = 0 := by
    intro x hx
    rw [hJ, Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      intro c
      have h1 : e (c * algebraMap R B' r) = e c * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      have h2 : e (e c * algebraMap R B' r) = e (e c) * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      rw [h1, h2, ← sub_mul]
      exact hJ2 _ (hu c) _ (Ideal.mem_map_of_mem _ hr)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have := hx c
      have := hy c
      rw [mul_add, map_add, map_add]
      linear_combination hx c + hy c
    | smul a x _ hx =>
      intro c
      rw [smul_eq_mul, ← _root_.mul_assoc]
      exact hx (c * a)
  have hrec : ∀ c, e (e (e (e c))) - 2 * e (e (e c)) + e (e c) = 0 := by
    intro c
    have := hkill _ (hu c) 1
    simp only [_root_.one_mul, map_sub] at this
    linear_combination this
  let e' : B' →ₐ[R] B' :=
    { toFun := fun b => 3 * e (e b) - 2 * e (e (e b))
      map_one' := by simp; norm_num
      map_mul' := by
        intro x y
        have h := hJ2 _ (hu (e x)) _ (hu (e y))
        simp only [map_mul]
        linear_combination (-6 : B') * h
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add]; ring
      commutes' := by intro r; simp only [AlgHom.commutes]; ring }
  refine ⟨e', ?_, ?_⟩
  · intro b
    show 3 * e (e (3 * e (e b) - 2 * e (e (e b)))) - 2 * e (e (e (3 * e (e b) - 2 * e (e (e b))))) = 3 * e (e b) - 2 * e (e (e b))
    simp only [map_sub, map_mul, map_ofNat]
    linear_combination (-3 : B') * hrec b + (-4 : B') * hrec (e b) + (4 : B') * hrec (e (e b))
  · intro b
    show p' (3 * e (e b) - 2 * e (e (e b))) = e₀ (p' b)
    simp only [map_sub, map_mul, map_ofNat, he, he₀]
    ring

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntNe
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMSep

theorem exists_int_ne' : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i j, i ≠ j → ∃ b : 𝓞 (FR E), φ i ((b : FR E) : E) ≠ φ j ((b : FR E) : E) :=
  fun {E} _ _ _ {I} φ hφ i j hij => exists_int_ne E I φ hφ i j hij

end GlobalTheory.CMSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralProjectiveClosureOfLinearSystemPoi
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

private theorem exists_toField {Ω : Type} [Field Ω] {Y : Scheme.{0}} [IsIntegral Y] (g : Sp Ω ⟶ Y) [IsDominant g] :
    ∃ φ : Y.functionField →+* Ω, (∀ U : Y.Opens, genericPoint Y ∈ U → ⊤ ≤ g ⁻¹ᵁ U) ∧
      (∀ U : Y.Opens, ⊤ ≤ g ⁻¹ᵁ U → genericPoint Y ∈ U) ∧
      ∀ (U : Y.Opens) (h : genericPoint Y ∈ U) (e : ⊤ ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)),
        ProjSpace.fnOn ⊤ (φ (Cartier.fnOf U h s)) = (g.appLE U ⊤ e).hom s := by
  have hI : IsIntegral (Sp Ω) := inferInstanceAs (IsIntegral (Spec (CommRingCat.of Ω)))
  have hS : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  let η := genericPoint (Sp Ω)
  have hb : Function.Bijective (Cartier.fnOf (X := Sp Ω) ⊤ trivial) := by
    refine ⟨fnOf_injective _ _, fun a => ?_⟩
    obtain ⟨U, hU, s, hs⟩ := (Sp Ω).presheaf.germ_exist (x := η) a
    obtain rfl : U = ⊤ := top_unique fun x _ => (Subsingleton.elim η x) ▸ hU
    exact ⟨s, hs⟩
  let e₁ := RingEquiv.ofBijective _ hb
  let e₂ := RingEquiv.ofBijective _ (ProjSpace.fnOn_top_bijective (A := Ω))
  refine ⟨(e₂.symm.toRingHom.comp e₁.symm.toRingHom).comp (functionFieldMap g), fun U hU x _ => ?_,
    fun U hU => gen_mem (x := g η) (hU trivial), fun U h e s => ?_⟩
  · obtain ⟨_, hz, z, rfl⟩ := g.denseRange.inter_open_nonempty U U.isOpen ⟨_, hU⟩
    exact (Subsingleton.elim z x) ▸ hz
  · change e₂ (e₂.symm (e₁.symm (functionFieldMap g _))) = _
    rw [RingEquiv.apply_symm_apply, RingEquiv.symm_apply_eq]
    have hx : η ∈ g ⁻¹ᵁ U := e trivial
    change _ = Cartier.fnOf ⊤ trivial (resG _ e (g.app U s))
    refine Eq.trans ?_ (fnOf_resG e _ _).symm
    rw [← Cartier.algebraMap_germ (show g η ∈ U from hx), functionFieldMap_algebraMap,
      ← Cartier.algebraMap_germ hx]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply g U η hx s

private theorem dim_of_trdeg {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {Y : Scheme.{0}} [IsIntegral Y]
    (q : Y ⟶ Sp K) [LocallyOfFiniteType q] (e : Y.functionField ≃+* Ω)
    (he : ∀ a, e (toFunctionField q a) = algebraMap K Ω a) {D : ℕ} (hD : Algebra.trdeg K Ω = D) :
    topologicalKrullDim Y = D := by
  letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ q)).hom.toAlgebra
  have hc : Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ q) = CommRingCat.ofHom (toFunctionField q) :=
    Spec.map_injective ((Spec.map_preimage _).trans (genericFieldPoint_over q))
  let e' : Y.functionField ≃ₐ[K] Ω := { e with
    commutes' := fun a => (congrArg (fun f => e (CommRingCat.Hom.hom f a)) hc).trans (he a) }
  have ht : Algebra.trdeg K Y.functionField = D :=
    (le_antisymm (trdeg_le_of_injective e'.toAlgHom e'.injective)
      (trdeg_le_of_injective e'.symm.toAlgHom e'.symm.injective)).trans hD
  have h1 := GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq q ht
  have h2 : (q ⁻¹' {genericPoint (Spec (CommRingCat.of K))} : Set Y) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
  rwa [h2, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph] at h1

private theorem eq_top_of_span {K V Ω ι : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (u : ι → V) (hu : Submodule.span K (Set.range u) = ⊤) (hg : GlobalTheory.DegVal.GenRatios ev)
    (L : Subfield Ω) (hc : ∀ a, algebraMap K Ω a ∈ L) (hr : ∀ k l, ev (u l) ≠ 0 → ev (u k) / ev (u l) ∈ L) :
    L = ⊤ := by
  obtain ⟨l, hl⟩ : ∃ l, ev (u l) ≠ 0 := by
    by_contra! h0
    exact hg.1 (LinearMap.ext_on_range hu fun k => by simpa using h0 k)
  have key : ∀ v, ev v / ev (u l) ∈ L := fun v => by
    have hv : v ∈ Submodule.span K (Set.range u) := hu ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hr k l hl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_div]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def, mul_div_assoc]; exact mul_mem (hc a) hx
  have h : GlobalTheory.DegVal.ratioField ev ≤ L.toIntermediateField hc := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨v, w, rfl⟩
    rw [← div_div_div_cancel_right₀ hl]
    exact div_mem (key v) (key w)
  rw [hg.2] at h
  exact top_unique fun x _ => h (IntermediateField.mem_top (x := x))

open MvPolynomial in

private theorem trdeg_eq {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (D : ℕ) (hg : GlobalTheory.DegVal.GenRatios ev) (hD : 0 < imageDeg ev D) :
    Algebra.trdeg K Ω = D := by
  obtain ⟨N, b, F, hF⟩ := (imageDeg_pos_iff ev D).1 hD
  set y : Fin N → Ω := fun j => ev (b j) with hy
  have hy0 : y ≠ 0 := fun h0 => hg.1 (b.ext fun k => by simpa using congrFun h0 k)
  have hr : Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤ :=
    eq_top_of_span ev b b.span_eq hg _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun k l _ => Subfield.subset_closure (Or.inr ⟨k, l, rfl⟩)
  have := isPrime_coneIdeal (K := K) y
  have hk : ringKrullDim (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = (D + 1 : ℕ) :=
    GlobalTheory.ChowExists.ringKrullDim_of_isChowFormInt (P := coneIdeal K y) (fun g hg n =>
      (mem_coneIdeal_of_isHomogeneous y (homogeneousComponent_isHomogeneous n g)).2
        ((mem_coneIdeal_iff y g).1 hg n)) hF
  obtain ⟨d, hd, hd'⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (MvPolynomial (Fin N) K ⧸ coneIdeal K y)
  obtain rfl : d = D + 1 := by exact_mod_cast hd.symm.trans hk
  let f := Ideal.kerLiftAlg (coneMap K y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = Algebra.trdeg K A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := GlobalTheory.Adelic.ConeDim.isAlgebraic_of_closure_eq_top y hy0 hr A hXy
  have : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top K A (Polynomial Ω), ← trdeg_add_eq K Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain] at hd'
  exact Cardinal.add_one_inj.1 (by exact_mod_cast hd')

theorem _root_.GlobalTheory.T.exists_integral_projective_closure_of_linearSystem_point : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (D m : ℕ) (u : Fin (m + 1) → V),
    Submodule.span K (Set.range u) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (q : Y ⟶ Sp K) (B : LB Y) (_ : B.IsLB) (t : Fin (m + 1) → B.Sec) (ψ : Ω →+* Y.functionField),
      IsProjOver q ∧ topologicalKrullDim Y = D ∧ (⨆ k, nonzeroLocus (t k) = ⊤) ∧ Function.Bijective ψ ∧
      (∀ a : K, ψ (algebraMap K Ω a) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX q ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : B.ι) (h : genericPoint Y ∈ B.U i),
        ψ (ev (u k)) * fnOf _ h ((t l).f i) = ψ (ev (u l)) * fnOf _ h ((t k).f i) := by
  intro K V Ω _ _ _ _ _ ev D m u hu hg hD
  set y : Fin (m + 1) → Ω := fun k => ev (u k) with hy_def
  have hy : Ideal.span (Set.range y) = ⊤ := by
    obtain ⟨l, hl⟩ : ∃ l, ev (u l) ≠ 0 := by
      by_contra! h0
      exact hg.1 (LinearMap.ext_on_range hu fun k => by simpa using h0 k)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨l, rfl⟩) (Ne.isUnit hl)
  let p := ProjSpace.pt (algebraMap K Ω) y hy
  have hI : IsIntegral (Sp Ω) := inferInstanceAs (IsIntegral (Spec (CommRingCat.of Ω)))
  have hS : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have hqc : QuasiCompact p := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  obtain ⟨Y, hY, g, j, hdom, hj, hgj⟩ : ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (g : Sp Ω ⟶ Y) (j : Y ⟶ PSpace K m),
      IsDominant g ∧ IsClosedImmersion j ∧ g ≫ j = p :=
    ⟨p.image, isIntegral_image p, p.toImage, p.imageι, inferInstance, inferInstance, p.toImage_imageι⟩
  obtain ⟨φ, hm₁, hm₂, hφ⟩ := exists_toField g
  let B := (ProjSpace.O1 K m).pull j
  let t : Fin (m + 1) → B.Sec := fun k => Cartier.secPull (ProjSpace.coord K m k) j
  have hU : ∀ i : PUnit → Fin (m + 1), g ⁻¹ᵁ B.U i = ProjSpace.spOpen (y (i ⟨⟩)) := fun i => by
    rw [← ProjSpace.pt_preimage_chart (algebraMap K Ω) y hy]
    refine (congrArg (g ⁻¹ᵁ ·) (pull_U (ProjSpace.O1 K m) j i)).trans ?_
    exact (Scheme.Hom.comp_preimage g j _).symm.trans (congrArg (· ⁻¹ᵁ _) hgj)
  have hmem : ∀ i : PUnit → Fin (m + 1), genericPoint Y ∈ B.U i ↔ y (i ⟨⟩) ≠ 0 := fun i => by
    constructor
    · intro h h0
      have := (hm₁ _ h).trans (hU i).le (show genericPoint (Sp Ω) ∈ (⊤ : (Sp Ω).Opens) from trivial)
      rw [ProjSpace.mem_spOpen, h0] at this
      exact this (zero_mem _)
    · intro h
      refine hm₂ _ (le_of_le_of_eq (fun x _ => ?_) (hU i).symm)
      exact fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (Ne.isUnit h))
  have hrat : ∀ (i : PUnit → Fin (m + 1)) (h : genericPoint Y ∈ B.U i) (l : Fin (m + 1)),
      φ (Cartier.fnOf _ h ((t l).f i)) * y (i ⟨⟩) = y l := fun i h l => by
    refine ProjSpace.fnOn_top_bijective.1 ?_
    have e₁ := (resG_self _ _).symm.trans (ProjSpace.resG_secPull_coord j l i le_rfl)
    have h' : ⊤ ≤ p ⁻¹ᵁ ProjSpace.chart K m (i ⟨⟩) :=
      (hm₁ _ h).trans ((hU i).trans (ProjSpace.pt_preimage_chart (algebraMap K Ω) y hy _).symm).le
    rw [map_mul, hφ _ h (hm₁ _ h), ← ProjSpace.pullRatio_pt_mul (algebraMap K Ω) y hy (i ⟨⟩) l h']
    congr 1
    refine (congrArg _ e₁).trans ?_
    rw [ProjSpace.appLE_pullRatio]
    exact ProjSpace.pullRatio_of_eq hgj _ _
  have hconst : ∀ a, φ (toFunctionField (j ≫ PSpace.str K m) a) = algebraMap K Ω a := fun a => by
    refine ProjSpace.fnOn_top_bijective.1 ?_
    refine (hφ ⊤ trivial le_top (((Scheme.ΓSpecIso (.of K)).inv ≫ (j ≫ PSpace.str K m).appTop).hom a)).trans ?_
    have e : g ≫ j ≫ PSpace.str K m = spMap (algebraMap K Ω) := by
      rw [reassoc_of% hgj, ProjSpace.pt_str]
    have e' : (j ≫ PSpace.str K m).appTop ≫ g.appTop = (spMap (algebraMap K Ω)).appTop := by
      rw [← Scheme.Hom.comp_appTop, e]
    have e'' := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K Ω))
    rw [← e'] at e''
    exact congrArg (resG (Sp Ω) le_top) (congrArg (fun f => f.hom a) e'').symm
  have hsurj : Function.Surjective φ := by
    rw [← RingHom.fieldRange_eq_top_iff]
    refine eq_top_of_span ev u hu hg _ (fun a => ⟨_, hconst a⟩) fun k l hl => ?_
    exact ⟨_, eq_div_of_mul_eq hl (hrat (fun _ => l) ((hmem (fun _ => l)).2 hl) k)⟩
  let e : Y.functionField ≃+* Ω := RingEquiv.ofBijective φ ⟨RingHom.injective _, hsurj⟩
  have hft : LocallyOfFiniteType (j ≫ PSpace.str K m) := inferInstance
  refine ⟨Y, hY, j ≫ PSpace.str K m, B, LB.isLB_pull (ProjSpace.O1_isLB K m) _, t,
    e.symm.toRingHom, ⟨m, j, hj, rfl⟩, dim_of_trdeg _ e hconst (trdeg_eq ev D hg hD),
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord K m) _, e.symm.bijective, fun a => ?_,
    fun k l i h => ?_⟩
  · apply e.injective
    change e (e.symm _) = φ _
    rw [RingEquiv.apply_symm_apply, ← hconst]
    simp [toFunctionField, Cartier.fnOf, algX, Scheme.Hom.appLE]
  · apply e.injective
    have hi := (hmem i).1 h
    change e (e.symm (y k) * _) = e (e.symm (y l) * _)
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    change y k * φ _ = y l * φ _
    rw [eq_div_of_mul_eq hi (hrat i h l), eq_div_of_mul_eq hi (hrat i h k)]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSeparatedProjModelGradedFunctionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_separated_projModel_gradedFunctions : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  first | exact @GlobalTheory.Desc.exists_model | exact GlobalTheory.Desc.exists_model | (intros; apply GlobalTheory.Desc.exists_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAddChiEq
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CobChi

theorem exists_isAdd_chi_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (n : ℕ), (n : R) = 0 → ∀ (u f : Fn1 A) (g : Fn2 A), IsAdd u g → Cohom (whole A) u f → ∃ g' : Fn2 A, IsAdd f g' ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → GlobalTheory.PtExt.chi n g' D x = GlobalTheory.PtExt.chi n g D x := by
  intro R _ A _ n hn u f g hu ⟨k, hk⟩
  have hf : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (x : Pt A D), f D D' φ x = u D D' φ x - (k D' (spOver φ ≫ x) - φ (k D x)) := by
    intro D _ _ D' _ _ φ x
    have h := hk D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg] at h
    linear_combination -h
  refine ⟨fun D _ _ x y ↦ g D x y - (k D (x * y) - k D x - k D y), ?_, ?_⟩
  · intro D _ _ D' _ _ φ x y
    have h1 := hu D D' φ x y
    simp only [hf, comp_mul, map_sub]
    linear_combination h1
  · intro D _ _ x hx
    have hnD : (n : D) = 0 := by
      rw [← map_natCast (algebraMap R D) n, hn, map_zero]
    have hs : ∑ i ∈ Finset.range n, (k D (x ^ i * x) - k D (x ^ i) - k D x) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      simp_rw [← pow_succ]
      rw [Finset.sum_range_sub (fun i ↦ k D (x ^ i)), hx, pow_zero, sub_self, zero_sub, neg_eq_zero, nsmul_eq_mul,
        hnD, zero_mul]
    simp only [GlobalTheory.PtExt.chi]
    rw [Finset.sum_sub_distrib, hs, sub_zero]

end GlobalTheory.CobChi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBundleFramesChartsChangeBasisStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieBundle_frames_charts_change_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∃ f : ∀ M : GlobalTheory.Reg.MChart Y, Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), (∀ M, GlobalTheory.VB.IsFrame (f M)) ∧ ∀ (M M' : GlobalTheory.Reg.MChart Y) (j : Fin M'.n), GlobalTheory.Twist.resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) = ∑ i, GlobalTheory.FlagMod.chg M M' i j • GlobalTheory.Twist.resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i) := by
  first | exact @GlobalTheory.ChartLieFrame.exists_lieFrame | exact GlobalTheory.ChartLieFrame.exists_lieFrame | (intros; apply GlobalTheory.ChartLieFrame.exists_lieFrame <;> assumption)
end

