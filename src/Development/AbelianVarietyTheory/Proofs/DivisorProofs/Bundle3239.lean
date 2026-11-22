import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3160
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBoundaryDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliarySetFieldDataCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbLocusIffOfMonomialTau
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.MonoAb

theorem exists_pos_of_ne_zero {X : Type} [AddCommGroup X] (d : LinearMap.BilinForm ℤ X)
    (hs : ∀ a b, d a b = d b a) (hn : ∀ a, 0 ≤ d a a) (h : d ≠ 0) : ∃ y, 0 < d y y := by
  by_contra hc
  push_neg at hc
  apply h
  ext a b
  have h1 := hc (a + b)
  have h2 : d a a = 0 := le_antisymm (hc a) (hn a)
  have h3 : d b b = 0 := le_antisymm (hc b) (hn b)
  have h4 := hn (a + b)
  have h5 : d (a + b) (a + b) = 0 := le_antisymm h1 h4
  simp only [map_add, LinearMap.add_apply, h2, h3, hs b a] at h5
  simp only [LinearMap.zero_apply]
  omega

end GlobalTheory.Mum.MonoAb

theorem GlobalTheory.Mum.abLocus_iff_of_monomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsMumPol Q G P → ∀ (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), (∀ k, t k ∈ maximalIdeal R ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → (∀ k, δ k ≠ 0) → Q.IsMonomialTau t δ → ∀ p : Sp R, p ∈ abLocus G ↔ ∏ k, t k ∉ p.asIdeal := by
  intro R _ _ _ hR Q _ G _ _ P hM m t δ ht hsymm hnn hdef hne hmono p
  obtain ⟨R', _, _, _, ρ, r, D, e, hR', hinj, hfin, -, hr, href, hmon⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised R Q m t δ hR hmono (fun k => (ht k).1) (fun k => (ht k).2)
      (fun k a b => hsymm k a b) hnn hdef
  obtain ⟨-, -, hG, -, hU⟩ := hM
  obtain ⟨G', _, _, π, -, A, U, hpb, -, -⟩ := hU R' ρ hR' hinj hfin D e href
  have hG' : IsSemiAbelian G' := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG
  haveI : IsNoetherianRing R' := hR'.1

  obtain ⟨q, hq⟩ : ∃ q : Sp R', spMap ρ q = p := by
    letI := ρ.toAlgebra
    haveI : p.asIdeal.IsPrime := p.isPrime
    haveI : Module.Finite R R' := hfin
    obtain ⟨Q', -, hQ', hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal R') (by
      intro x hx
      have : ρ x = 0 := hx
      rw [show x = 0 from hinj (this.trans (map_zero ρ).symm)]
      exact p.asIdeal.zero_mem)
    exact ⟨⟨Q', hQ'⟩, PrimeSpectrum.ext hc⟩
  subst hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  rw [abLocus_pullback abLocusOne hG hpb.1 q]
  have key : ∏ k, t k ∈ (spMap ρ q).asIdeal ↔ ∏ k, r k ∈ q.asIdeal := by
    show ρ (∏ k, t k) ∈ q.asIdeal ↔ _
    rw [map_prod, show (∏ k, ρ (t k)) = (∏ k, r k) ^ 2 by rw [← Finset.prod_pow]; simp only [hr]]
    exact ⟨fun h => q.isPrime.mem_of_pow_mem 2 h, fun h => Ideal.pow_mem_of_mem _ h 2 (by norm_num)⟩
  rw [key]
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have ho : IsOpen (abLocus G') := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G' hG'
  constructor
  · intro hab hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    obtain ⟨y, hy⟩ := GlobalTheory.Mum.MonoAb.exists_pos_of_ne_zero (δ k) (hsymm k) (hnn k) (hne k)
    obtain ⟨u, n, hn, hc⟩ := hmon (e.symm y)
    have hnk : 0 < n k := by
      have := hn k
      simp [pull] at this
      omega
    have hUo := GlobalTheory.PsiAbelian.psiUnitOn_abLocus h1 h2 h3 h4 h5 R' _ (GlobalTheory.SiegChart.isAdmissibleBase_of_completeNormalLocalCharZero hR') D A G' hG' U ho
      (e.symm y)
    refine GlobalTheory.PsiCoordLocal.not_mem_of_coord ho hab hUo hc ?_
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
      (Ideal.pow_mem_of_mem _ hk _ hnk)
  · intro hnot
    let W : (Sp R').Opens := ⟨{x | ∏ k, r k ∉ x.asIdeal}, (PrimeSpectrum.basicOpen (∏ k, r k)).isOpen⟩
    exact GlobalTheory.Mum.UnifFibre.fibres_abelian_of_psiUnitOn R' ⟨admissibleBase_of_completeNormalLocalCharZero hR', hR'.2.2.2⟩ D A G' hG' U W
      (fun y => hmon.psiUnitOn y fun x hx => hx) hnot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructure
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem unobDim_of_formSt : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  intro hF hP hA R _ I hI R₀ _ π hπ hk A₀ _ g hab hsm
  obtain ⟨X, i, hpb, hsmX⟩ := GlobalTheory.T.exists_smooth_lift_abelian_scheme_square_zero hF hP R R₀ I hI π hπ hk A₀ g hab hsm
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
  have h1 : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ A₀.hom = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀)
  obtain ⟨e, he, he'⟩ := GlobalTheory.SecLift.exists_section_lift R R₀ π hπ hnil X A₀ i hpb hsmX _ h1
  have P := IsPullback.of_hasPullback X.hom X.hom
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    simp only [Category.assoc, hpb.w]
    rw [← Category.assoc, ← Category.assoc, Over.w (fst A₀ A₀), Over.w (snd A₀ A₀)]
  let l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left := P.lift _ _ w
  have l1 : l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := P.lift_fst _ _ w
  have l2 : l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := P.lift_snd _ _ w
  obtain ⟨m, hm⟩ := GlobalTheory.T.multiplication_lifts_square_zero_smooth_lift hF hA R R₀ I hI π hπ hk A₀ g hab hsm X i hpb hsmX e he he' l l1 l2
  obtain ⟨G, hG, hab'⟩ := GlobalTheory.LiftGroupLaw.exists_grpObj_isAbelianScheme R R₀ π hπ hnil A₀ hab X i hpb hsmX e he he'
    l l1 l2 m hm
  exact ⟨X, G, i, hG, hab'⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrablePolynomialVanishing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreProj

theorem pol_archInt_pull_eq_zero : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), GenSmooth q d → IsArithVar p D → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β → ∀ (L : α → HermLB p) (A : β → HermLB q) (M : HermLB p) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).ArchIntegrable M D hr) → pol (fun n => (comb (Sum.elim L fun a => (A a).pull f w) n).archInt M D hr) = 0 := by
  classical
  intro k _ B Y _ q p d D hB hX f w α β _ _ hd L A M r hr hint
  set F : α ⊕ β → HermLB p := Sum.elim L fun a => (A a).pull f w with hF
  haveI := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  simp only [HermLB.archInt, finsum_eq_sum_of_fintype]
  rw [pol_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  unfold pol
  refine GlobalTheory.T.chern_integral_linear_relation_zero k Y p hX.isProjOver σ D (Finset (α ⊕ β)) _ _ ?_ _ _ fun S => hint _ σ
  intro c y hy
  obtain ⟨R⟩ := hB σ
  obtain ⟨i, hi⟩ := R.cover (PtsOver.map f w (spMap σ) y)
  obtain ⟨P, Q, hPQ⟩ := GlobalTheory.T.pullback_chart_metric_block_form k B Y q p f w σ D d c (R.chart i) y hy hi
  choose K hK using fun b => hPQ (A b) (pick (((A b).pull f w).φ σ).isLB y) (mem_pick _ y)
  set m : ∀ l, (F l).B.ι := fun l => pick ((F l).φ σ).isLB y with hm
  have hK' : ∀ b, c.hess ((F (Sum.inr b)).φ σ) (m (Sum.inr b)) y = P * K b * Q := hK
  have key : ∀ n : α ⊕ β → ℤ, c.chernDens ((comb F n).φ σ) y = D.factorial / Real.pi ^ D *
      (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • c.hess ((F (Sum.inl a)).φ σ) (m (Sum.inl a)) y +
        ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re := by
    intro n
    rw [AlgChart.chernDens, GlobalTheory.Mean4O.ReadsProj.hess_comb F n σ c hy _ (mem_pick _ y) m
      (fun l => mem_pick _ y), Fintype.sum_sum_type]
    simp only [hK']
  simp only [key]
  have h0 := pol_const_mul (D.factorial / Real.pi ^ D) (fun n : α ⊕ β → ℤ =>
      (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • c.hess ((F (Sum.inl a)).φ σ) (m (Sum.inl a)) y +
        ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re)
  rw [GlobalTheory.T.polynomial_det_hermitian_sum_zero D d α β hd, mul_zero] at h0
  unfold pol at h0
  exact h0

end GlobalTheory.FibreProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanProjInclRational
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatTorusAct

open scoped IntermediateField

theorem finrank_adjoin_sqrt_neg {E : Type} [Field E] [CharZero E] (d : ℕ) (hd : 0 < d) (w : E) (hw : w ^ 2 = -(d : E)) :
    Module.finrank ℚ ℚ⟮w⟯ = 2 := by
  have hint : IsIntegral ℚ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hw]
  rw [IntermediateField.adjoin.finrank hint]
  have hdvd : minpoly ℚ w ∣ Polynomial.X ^ 2 + Polynomial.C (d : ℚ) := minpoly.dvd _ _ (by simp [hw])
  have hle : (minpoly ℚ w).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X_pow_add_C (d : ℚ) (by norm_num)).ne_zero
    rwa [Polynomial.natDegree_X_pow_add_C] at this
  have hpos := minpoly.natDegree_pos hint
  have hne : (minpoly ℚ w).natDegree ≠ 1 := by
    intro h1
    obtain ⟨q, hq⟩ := (minpoly.natDegree_eq_one_iff).1 h1
    have h2 : ((q ^ 2 : ℚ) : E) = ((-(d : ℚ) : ℚ) : E) := by
      rw [Rat.cast_pow]; push_cast
      have : (algebraMap ℚ E q) = (q : E) := rfl
      rw [← this, hq, hw]
    have h3 : q ^ 2 = -(d : ℚ) := Rat.cast_injective h2
    have h4 : (0 : ℚ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg q]
  omega

theorem ringHom_ext_adjoin {E R : Type} [Field E] [CharZero E] [Field R] [CharZero R] (w : E)
    (f g : ℚ⟮w⟯ →+* R) (h : f (IntermediateField.AdjoinSimple.gen ℚ w) = g (IntermediateField.AdjoinSimple.gen ℚ w)) : f = g := by
  have : f.toRatAlgHom = g.toRatAlgHom := by
    refine IntermediateField.adjoin_algHom_ext ℚ ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h
  ext x
  exact DFunLike.congr_fun this x

theorem exists_unif_act_orderC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α := by
  intro E _ _ _ I _ d φ hF c y hc
  obtain ⟨hdp, -, -, -, -, hcard, hcm, w, hw, hφw⟩ := hF
  have hd : 0 < d := hdp.pos
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hI
  let δ : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w
  have hδ : δ ^ 2 = -(d : ℚ⟮w⟯) := Subtype.ext (by simpa [δ] using hw)
  have hagree : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) = (φ i₀).comp (algebraMap ℚ⟮w⟯ E) := fun i ↦
    ringHom_ext_adjoin w _ _ (by
      show φ i w = φ i₀ w
      rw [hφw, hφw])
  obtain ⟨𝔠, X, U, -⟩ := GlobalTheory.T.cm_abelian_variety_uniformization_exists ℚ⟮w⟯ d δ ((φ i₀).comp (algebraMap ℚ⟮w⟯ E))
    (finrank_adjoin_sqrt_neg d hd w hw) hd hδ E I φ hcm hagree c y hc
  refine ⟨𝔠, X, U, fun a ↦ ?_⟩
  let T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun v j ↦ φ (U.e j) (a : E) * v j
      map_add' := fun v v' ↦ by ext j; simp [mul_add]
      map_smul' := fun s v ↦ by ext j; simp; ring }
  have hT : ∀ v ∈ U.u.Λ, T v ∈ U.u.Λ := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (U.lat v).1 hv
    refine (U.lat _).2 ⟨(a : E) * x, mul_mem_lattice a.2 hx, ?_⟩
    ext j
    simp [T, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  obtain ⟨α, hα, hαe⟩ := GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice (FR E) 𝔠 X _ _ U.u T hT
  exact ⟨α, hα, hαe⟩

end GlobalTheory.LatTorusAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliarySetFieldDataCongruenceStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliary_set_field_data_congruence : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∃ ξ : E, GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ ∧
      ∀ i, U.h i ≠ 0 ∧ ψ (ev i) (yv i) * (2 * Complex.I * φ i ξ) = (U.h i : ℂ) * ((ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) : R) : ℂ) := by
  first | exact @GlobalTheory.RatioForm.form_ratio | exact GlobalTheory.RatioForm.form_ratio | (intros; apply GlobalTheory.RatioForm.form_ratio <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePointAndExponentialHolomorphicInPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELUHol

open GlobalTheory.HolPeriods

theorem isHolTo_point_and_exp : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), 3 ≤ N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → C D' t → FullMark N D' t → IsOpen B → IsHolPeriods D' ρ B P → (∀ b ∈ B, UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b)) → IsHolTo B y ∧ IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
  intro O _ bar g ρ Λ F N C d D' t m B P y e hN heta hsm hqc hfine hC hfull hB hP hU
  have hN0 : 0 < N := by omega
  have hrefl : IsMarkedIsom N D' D' t t (LinearEquiv.refl O D'.La) :=
    ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩⟩
  have uniq : ∀ {Q Q' : D'.La →+ (Fin g → ℂ)} {x x' : Sp ℂ ⟶ F.X}
      {u : (Fin g → ℂ) → (Over.mk x ⟶ F.A)} {u' : (Fin g → ℂ) → (Over.mk x' ⟶ F.A)},
      UnifAt F (RingHom.id ℂ) ρ N D' t Q x u → UnifAt F (RingHom.id ℂ) ρ N D' t Q' x' u' →
      ∀ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, Q' a = k (Q a)) → x = x' := by
    intro Q Q' x x' u u' h h' k hk
    exact hfine.sep D' D' t t Q Q' x x' u u' h h' (LinearEquiv.refl O D'.La) k hrefl fun a => hk a
  have expo : ∀ {Q Q' : D'.La →+ (Fin g → ℂ)} {x x' : Sp ℂ ⟶ F.X}
      {u : (Fin g → ℂ) → (Over.mk x ⟶ F.A)} {u' : (Fin g → ℂ) → (Over.mk x' ⟶ F.A)},
      UnifAt F (RingHom.id ℂ) ρ N D' t Q x u → UnifAt F (RingHom.id ℂ) ρ N D' t Q' x' u' →
      ∀ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, Q' a = k (Q a)) →
      ∀ z, (show Sp ℂ ⟶ F.A.left from (u z).left) = (u' (k z)).left := by
    intro Q Q' x x' u u' h h' k hk z
    obtain rfl := uniq h h' k hk
    have h2 := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' D' t t Q Q' x u (LinearEquiv.refl O D'.La) k
      hN0 h hrefl (fun a => hk a) h'.2.1
    have h3 := congrFun (GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' t Q' x _ _ hN hfull h2 h') (k z)
    simp only [LinearEquiv.symm_apply_apply] at h3
    rw [h3]
  have near : ∀ {n : ℕ} {C' : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → (D'.La →+ (Fin g → ℂ))}
      (P₀ : D'.La →+ (Fin g → ℂ)) (s : Finset D'.La) (ε : ℝ), IsOpen C' → IsHolPeriods D' ρ C' R →
      IsOpen {c | c ∈ C' ∧ ∀ x ∈ s, ‖R c x - P₀ x‖ < ε} := by
    intro n C' R P₀ s ε hC' hR
    refine isOpen_iff_mem_nhds.2 fun c hc => ?_
    refine Filter.Eventually.and (hC'.mem_nhds hc.1) ((Filter.eventually_all_finset s).2 fun x hx => ?_)
    have : ContinuousAt (fun c => ‖R c x - P₀ x‖) c :=
      (((hR.2 x).continuousOn.continuousAt (hC'.mem_nhds hc.1)).sub continuousAt_const).norm
    exact this.eventually_lt continuousAt_const (hc.2 x hx)
  have loc : ∀ b₀ ∈ B, ∃ B' : Set (Fin m → ℂ), b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y ∧
      IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
    intro b₀ hb₀
    obtain ⟨d', hd'⟩ := GlobalTheory.T.exists_perCoord O bar g ρ D'
    have hdd : d = d' := GlobalTheory.T.smoothBase_dim_eq_periodSpace_dim O bar g ρ Λ F N C d d' D' t hN0 heta hsm hqc hfine hC ⟨_, hP.1 b₀ hb₀⟩ hd'
    subst hdd
    obtain ⟨C₀, y₁, -, -, -, -, hC₀, h0, hy0, hover, hhol, hinj, -⟩ :=
      GlobalTheory.SubfieldChart.exists_holomorphic_chart ℂ (RingHom.id ℂ) F.X F.s d (y b₀) hsm (hU b₀ hb₀).1
    obtain ⟨e₀, he₀⟩ : ∃ e₀, UnifAt F (RingHom.id ℂ) ρ N D' t (P b₀) (y₁ 0) e₀ := by
      rw [hy0]; exact ⟨_, hU b₀ hb₀⟩
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d _
    obtain ⟨C₁, P₁, e₁, hC₁, h01, hsub, hP0, hP₁, he₁, hU₁⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N D' t d C₀ y₁ 0 (P b₀) e₀ hN0 heta inferInstance hC₀ h0 hover hhol he₀
    obtain ⟨Bq, Q, Z, s, ε, hBq, hε, hQ, hZ0, hQZ, hZQ, hnear, hinv, hZ⟩ := hd' (P b₀) (hP.1 b₀ hb₀)
    have zinj : ∀ R R' : D'.La →+ (Fin g → ℂ), IsPeriod D' ρ R → IsPeriod D' ρ R' →
        (∀ x ∈ s, ‖R x - P b₀ x‖ < ε) → (∀ x ∈ s, ‖R' x - P b₀ x‖ < ε) → Z R = Z R' →
        ∃ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, R' a = k (R a) := by
      intro R R' hR hR' hn hn' hZZ
      obtain ⟨-, h, hh⟩ := hnear R hR hn
      obtain ⟨-, h', hh'⟩ := hnear R' hR' hn'
      refine ⟨h.symm.trans h', fun a => ?_⟩
      rw [hh' a, hh a, hZZ]
      simp
    set C₂ := {c | c ∈ C₁ ∧ ∀ x ∈ s, ‖P₁ c x - P b₀ x‖ < ε} with hC₂def
    have hC₂ : IsOpen C₂ := near (P b₀) s ε hC₁ hP₁
    have h02 : (0 : Fin d → ℂ) ∈ C₂ := ⟨h01, fun x _ => by simpa [hP0] using hε⟩
    have hF : DifferentiableOn ℂ (fun c => Z (P₁ c)) C₂ :=
      hZ _ C₂ P₁ hC₂ ⟨fun c hc => hP₁.1 c hc.1, fun x => (hP₁.2 x).mono fun c hc => hc.1⟩ fun c hc => hc.2
    have hFinj : Set.InjOn (fun c => Z (P₁ c)) C₂ := by
      intro c hc c' hc' hcc
      obtain ⟨k, hk⟩ := zinj _ _ (hP₁.1 c hc.1) (hP₁.1 c' hc'.1) hc.2 hc'.2 hcc
      exact hinj (hsub hc.1) (hsub hc'.1) (uniq (hU₁ c hc.1) (hU₁ c' hc'.1) k hk)
    obtain ⟨W, G, hW, hW0, hG, hGW⟩ :=
      exists_local_section hC₂ hF h02 (GlobalTheory.InjHol.bijective_fderiv_of_injOn _ C₂ _ hC₂ hF hFinj 0 h02)
    set B₁ := {b | b ∈ B ∧ ∀ x ∈ s, ‖P b x - P b₀ x‖ < ε} with hB₁def
    have hB₁ : IsOpen B₁ := near (P b₀) s ε hB hP
    have hZP : DifferentiableOn ℂ (fun b => Z (P b)) B₁ :=
      hZ _ B₁ P hB₁ ⟨fun c hc => hP.1 c hc.1, fun x => (hP.2 x).mono fun c hc => hc.1⟩ fun c hc => hc.2
    set B₂ := B₁ ∩ (fun b => Z (P b)) ⁻¹' W with hB₂def
    have hB₂ : IsOpen B₂ := hZP.continuousOn.isOpen_inter_preimage hB₁ hW
    have hb₂ : b₀ ∈ B₂ := ⟨⟨hb₀, fun x _ => by simpa using hε⟩, by simpa [hP0] using hW0⟩
    have hβ : DifferentiableOn ℂ (fun b => G (Z (P b))) B₂ :=
      hG.comp (hZP.mono Set.inter_subset_left) fun b hb => hb.2
    have hβC : ∀ b ∈ B₂, G (Z (P b)) ∈ C₂ := fun b hb => (hGW _ hb.2).1
    have hk : ∀ b, ∃ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), b ∈ B₂ → ∀ a, P₁ (G (Z (P b))) a = k (P b a) := by
      intro b
      by_cases hb : b ∈ B₂
      · obtain ⟨k, hk⟩ := zinj _ _ (hP.1 b hb.1.1) (hP₁.1 _ (hβC b hb).1) hb.1.2 (hβC b hb).2
          (hGW _ hb.2).2.symm
        exact ⟨k, fun _ => hk⟩
      · exact ⟨LinearEquiv.refl _ _, fun h => absurd h hb⟩
    choose k hk using hk
    obtain ⟨B₃, hB₃, hb₃, hsub₃, hkd⟩ := exists_differentiableOn_transfer (Q := P)
      (Q' := fun b => P₁ (G (Z (P b)))) hB₂ (fun x => (hP.2 x).mono fun b hb => hb.1.1)
      (fun x => (hP₁.2 x).comp hβ fun b hb => (hβC b hb).1) hb₂ (hP.1 b₀ hb₀).2.2.2.1
      (fun b => (k b).toLinearMap) fun b hb x => hk b hb x
    refine ⟨B₃, hb₃, fun b hb => (hsub₃ hb).1.1, ?_, ?_⟩
    · refine isHolTo_congr (isHolTo_comp hhol hB₃ (hβ.mono hsub₃)
        fun b hb => hsub (hβC b (hsub₃ hb)).1) fun b hb => ?_
      exact uniq (hU b (hsub₃ hb).1.1) (hU₁ _ (hβC b (hsub₃ hb)).1) (k b) (hk b (hsub₃ hb))
    · have hφ : DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (G (Z (P bz.1)), k bz.1 bz.2))
          (B₃ ×ˢ Set.univ) :=
        (hβ.comp differentiableOn_fst fun bz hbz => hsub₃ hbz.1).prodMk hkd
      refine isHolTo_congr (isHolTo_comp he₁ (hB₃.prod isOpen_univ) hφ
        fun bz hbz => ⟨(hβC _ (hsub₃ hbz.1)).1, trivial⟩) fun bz hbz => ?_
      exact expo (hU _ (hsub₃ hbz.1).1.1) (hU₁ _ (hβC _ (hsub₃ hbz.1)).1) (k bz.1)
        (hk _ (hsub₃ hbz.1)) bz.2
  refine ⟨isHolTo_of_local fun b hb => ?_, isHolTo_of_local fun bz hbz => ?_⟩
  · obtain ⟨B', h1, h2, h3, -⟩ := loc b hb
    exact ⟨B', h1, h2, h3⟩
  · obtain ⟨B', h1, h2, -, h4⟩ := loc bz.1 hbz.1
    exact ⟨B' ×ˢ Set.univ, ⟨h1, trivial⟩, Set.prod_mono h2 le_rfl, h4⟩

end GlobalTheory.PELUHol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcCompFinAwayPtOfNotMem
section
open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.WeilM GlobalTheory.LocIntw
open GlobalTheory GlobalTheory.LFun GlobalTheory.ThK GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWInt GlobalTheory.LocSW

noncomputable section
namespace GlobalTheory.AwayFix.Chart

open GlobalTheory.AwayFix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_smul_away (v : HeightOneSpectrum (𝓞 F)) (a : AF F) (z : AF F ⊗[F] E) :
    compFin F E v (a • z) = evFin F v a • compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F v) a b)
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem compInf_smul_away (w : InfinitePlace F) (a : AF F) (z : AF F ⊗[F] E) :
    compInf F E w (a • z) = evInf F w a • compInf F E w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F w) a b)
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

variable {σ : E →ₐ[F] E} {N : ℕ} {Q : Matrix (Fin N) (Fin N) E}

end GlobalTheory.AwayFix.Chart

namespace GlobalTheory.AwayFix

open GlobalTheory.AwayFix.Chart

end GlobalTheory.AwayFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectingStatementStatement
section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ConnectingStatement : BridgeSt := by
  first | exact @GlobalTheory.DetHT.Bridge.bridge | exact GlobalTheory.DetHT.Bridge.bridge | (intros; apply GlobalTheory.DetHT.Bridge.bridge <;> assumption)
end

