import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightPolynomialInDegrees
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.VertFun

noncomputable def iterD {ι : Type} : (m : ℕ) → (Fin m → ι) → (MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ)
  | 0, _ => LinearMap.id
  | m + 1, a => (MvPolynomial.pderiv (a 0)).toLinearMap ∘ₗ iterD m (Fin.tail a)

theorem pderiv_lin {ι : Type} [Fintype ι] (x : ι → ℝ) (j : ι) :
    MvPolynomial.pderiv j (lin x) = MvPolynomial.C (x j) := by
  rw [lin, map_sum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hb, hb.symm]
  · simp

theorem iterD_lin_pow {ι : Type} [Fintype ι] (x : ι → ℝ) (N : ℕ) : ∀ (m : ℕ) (a : Fin m → ι),
    iterD m a (lin x ^ N) = MvPolynomial.C ((N.descFactorial m : ℝ) * ∏ j, x (a j)) * lin x ^ (N - m)
  | 0, a => by simp [iterD]
  | m + 1, a => by
    rw [iterD, LinearMap.comp_apply, iterD_lin_pow x N m, Derivation.coeFn_coe, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_pow, pderiv_lin, Nat.descFactorial_succ, Fin.prod_univ_succ, Nat.sub_sub]
    simp only [Fin.tail, Nat.cast_mul, map_mul, map_natCast]
    ring

theorem exists_functional {ι : Type} [Fintype ι] (e : ℕ) (I : (Fin e → ι) → ℝ) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ x : ι → ℝ, T (lin x ^ e) = ∑ a : Fin e → ι, (∏ j, x (a j)) * I a := by
  refine ⟨∑ a : Fin e → ι, (I a / (e.factorial : ℝ)) • (MvPolynomial.lcoeff ℝ 0 ∘ₗ iterD e a), fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast e.factorial_ne_zero
  rw [LinearMap.smul_apply, LinearMap.comp_apply, iterD_lin_pow, Nat.sub_self, pow_zero, mul_one,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_zero_C, Nat.descFactorial_self, smul_eq_mul]
  field_simp

theorem topSelf_comb_pull {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {κ : Type} [Field κ]
    {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = D) (i : Z ⟶ X)
    {ι : Type} [Fintype ι] (N : ι → HermLB p) (n : ι → ℤ) :
    (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ) =
      ∑ a : Fin D → ι, (∏ j, (n (a j) : ℝ)) * (interNum κ (structureModule Z) (fun j => (N (a j)).B.pull i) : ℝ) := by
  have HD := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := D)
    (by rw [QCoh.suppDim_structureModule, hd])
  have hL : ∀ j, ((N j).B.pull i).IsLB := fun j => LB.isLB_pull (N j).isLB i
  have e := HD.interNum_of_cls_eq_sum (L := fun j => (N j).B.pull i) hL (Q := fun _ => (comb N n).B.pull i)
    (fun _ => LB.isLB_pull (comb N n).isLB i) (fun _ => n) fun _ => by
      rw [CechPic.cls_pull (comb N n).isLB, GenFibreSecs.cls_comb, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, CechPic.cls_pull (N j).isLB]
  rw [topSelf_def, e]
  push_cast
  rfl

theorem exists_vertical_functional : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra (ZMod ℓ) Γ(Z, ⊤)] (e : ℕ), topologicalKrullDim Z = e → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p),
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ e) := by
  intro k _ Y p D hY Z i _ _ ℓ _ _ e he ι _ L
  have hp := GlobalTheory.VertProj.isProjOver_strHom_zmod k Y p D hY Z i ℓ
  obtain ⟨T, hT⟩ := exists_functional e fun a : Fin e → ι =>
    (interNum (ZMod ℓ) (structureModule Z) (fun j => (L (a j)).B.pull i) : ℝ) * Real.log ℓ
  refine ⟨T, fun n g hg => ?_⟩
  rw [hg.vertical Z i (ZMod ℓ) e he, Nat.card_zmod, topSelf_comb_pull hp he i L n, hT, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

end GlobalTheory.VertFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyDivisorDimension
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.CodimOneDim

theorem le_of_add (D : ℕ) (a : ℕ∞) (r : WithBot ℕ∞) (ha : a = 1)
    (h : (((D + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) + r) : (D : WithBot ℕ∞) ≤ r := by
  subst ha
  induction r using WithBot.recBotCoe with
  | bot => simp at h
  | coe r =>
    induction r using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe r =>
      have : D + 1 ≤ 1 + r := by exact_mod_cast h
      exact_mod_cast (show D ≤ r by omega)

theorem topologicalKrullDim_eq_of_coheight_eq_one : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
    Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  intro k _ Y p D h Z i _ _ hz
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isIntegral
  obtain ⟨d, hd⟩ := h.exists_dim_eq i
  rw [hd]

  have hup : topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y :=
    GlobalTheory.DimCodim.dim_add_le_of_le_coheight (S := Y) (W := Z) i.continuous
      i.isClosedEmbedding.injective 1 fun w => by
        rw [← hz]
        exact Order.coheight_anti (genericPoint_specializes w |>.map i.continuous)
  rw [hd, h.dim_eq] at hup
  have hdD : d ≤ D := by
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hup
    have : d + 1 ≤ D + 1 := by exact_mod_cast this
    omega
  obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over p (i (genericPoint Z))
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨_, _, _⟩ := RegGenSmooth.chart_props h j hj
  have : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance inferInstance
  have hst : ringKrullDim (Y.presheaf.stalk (j q)) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hq, hz]; rfl
  let x : Spec (.of A) := q
  have : IsIso (j.stalkMap x) := inferInstance
  have e := (asIso (j.stalkMap x) ≪≫ Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv
  have hq1 : (q.asIdeal.height : WithBot ℕ∞) = 1 := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv e, hst]
  obtain ⟨_, hKA⟩ := RegGenSmooth.ringKrullDim_chart h
    (IsPullback.of_hasPullback p (spMap (algebraMap k (FractionRing k)))) j hj
  obtain ⟨M, _, hM⟩ := GlobalTheory.T.exists_maximal_height_succ_dim k A D hKA
  have h2 := GlobalTheory.T.height_maximal_le_prime_add_dim A q.asIdeal M
  have hM' : (((D + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
      (q.asIdeal.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q.asIdeal) :=
    (WithBot.coe_le_coe.2 hM).trans h2
  have hq1' : q.asIdeal.height = 1 := by exact_mod_cast hq1
  have hDq := le_of_add D _ _ hq1' hM'
  have hsub : (Set.range j ∩ closure {j q} : Set Y) ⊆ Set.range i := fun y hy =>
    closure_minimal (s := {j q}) (Set.singleton_subset_iff.2 (⟨genericPoint Z, hq.symm⟩ : j q ∈ Set.range i))
      i.isClosedEmbedding.isClosed_range hy.2
  have e₁ := topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding
    (rfl : Set.range i = Set.range i)
  have h3 : topologicalKrullDim (Set.range j ∩ closure {j q} : Set Y) ≤ topologicalKrullDim Z := by
    rw [← e₁]
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j q, hd] at h3
  have h4 : (D : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := hDq.trans h3
  have h5 : D ≤ d := by exact_mod_cast h4
  rw [show d = D by omega]
end GlobalTheory.CodimOneDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliarySetLAdicPlace
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.XiSize

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

variable (R : Subring ℂ) [IsDiscreteValuationRing R]

theorem ord_nonneg {y : FractionRing R} (hy : y ≠ 0)
    (h : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) y ≤ 1) : 0 ≤ ord_vw R y := by
  unfold ord_vw
  have h0 : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) y ≠ 0 := by simpa using hy
  have e := WithZero.exp_log h0
  rw [← e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

theorem ord_inv (y : FractionRing R) : ord_vw R y⁻¹ = - ord_vw R y := by
  unfold ord_vw
  rw [map_inv₀, WithZero.log_inv]

theorem ord_nonneg_of_mem {y : FractionRing R} (hy : y ≠ 0) (r : R) (hr : algebraMap R (FractionRing R) r = y) :
    0 ≤ ord_vw R y := by
  refine ord_nonneg R hy ?_
  rw [← hr]
  exact (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one r

theorem xi_size : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (R : Subring ℂ) [IsDiscreteValuationRing R],
    GlobalTheory.LatModel.IsPlaceRing E l lam R → ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (ξ : E) (e₀ : ℤˣ), ξ ∈ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polPos φ e₀ (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y) →
      GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ →
      ξ ≠ 0 ∧ ∀ σ : E →+* FractionRing R, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (σ ξ) ≤ 0 := by
  intro hPM E _ _ _ I _ d φ hFD 𝔣 h𝔣 l _ Q hQ hQl y hy lam R _ hR j hj ξ e₀ hξ hgen
  obtain ⟨-, -, hUn, -, -, -, hCM, -⟩ := hFD
  obtain ⟨hne, hint, -⟩ := (hPM E hUn I φ hCM e₀).2 𝔣 Q h𝔣 hQ l Fact.out hQl y hy ξ hξ hgen
  refine ⟨hne, fun σ => ?_⟩
  have hl : l.Prime := Fact.out
  have hσ : σ ξ ≠ 0 := (map_ne_zero σ).2 hne
  obtain ⟨n, hn, hI⟩ := hint (j.comp σ)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' ((Nat.coprime_zero_left l).1 hn)
  have hnd : ¬ l ∣ n := (Nat.Prime.coprime_iff_not_dvd hl).1 hn.symm

  have e1 : (n : ℂ) * ((j.comp σ) ξ)⁻¹ = j ((n : FractionRing R) * (σ ξ)⁻¹) := by
    simp [map_inv₀]
  have hIR : IsIntegral R ((n : FractionRing R) * (σ ξ)⁻¹) := by
    obtain ⟨p, hp, hev⟩ := hI
    refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    apply j.injective
    rw [Polynomial.hom_eval₂, ← e1, map_zero]
    have hs : j.comp ((algebraMap R (FractionRing R)).comp (Int.castRingHom R)) = algebraMap ℤ ℂ := Subsingleton.elim _ _
    rw [hs]
    exact hev
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hIR

  have hq : (((1 / n : ℚ)) : ℂ) ∈ R := hR.2.2.1 _ (by
    rw [one_div, padicValRat.inv, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]; simp)
  set u : R := ⟨_, hq⟩
  have hun : u * (n : R) = 1 := by
    apply Subtype.ext
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    simp [u]
    field_simp
  have e2 : algebraMap R (FractionRing R) (u * r) = (σ ξ)⁻¹ := by
    rw [map_mul, hr, ← _root_.mul_assoc, ← map_natCast (algebraMap R (FractionRing R)), ← map_mul, hun, map_one, _root_.one_mul]
  have h1 : ord_vw R (σ ξ) ≤ 0 := by
    have := ord_nonneg_of_mem R (inv_ne_zero hσ) _ e2
    rw [ord_inv] at this
    omega
  have hl0 : (l : FractionRing R) ≠ 0 := by
    rw [← map_natCast (algebraMap R (FractionRing R))]
    refine (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ?_
    intro h
    have := congrArg Subtype.val h
    simp [hl.ne_zero] at this
  have h2 : 0 ≤ ord_vw R (l : FractionRing R) :=
    ord_nonneg_of_mem R hl0 (l : R) (map_natCast _ _)
  unfold val_vp
  rw [if_neg hσ]
  have h3 : ((ord_vw R (σ ξ) : ℚ) / (ord_vw R (l : FractionRing R) : ℚ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact_mod_cast h3

end GlobalTheory.XiSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPosDefFiniteProjectiveLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balanced_posDef_finite_projective_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c), T.be ∈ balForms H.bar T.P.D.toPre.X ∧ (∀ y, y ≠ 0 → 0 < T.be y y) ∧ Module.Finite (𝓞 E) T.P.D.toPre.X ∧ Module.Projective (𝓞 E) T.P.D.toPre.X ∧ ∃ n : ℕ, Nonempty (T.P.D.toPre.X ≃ₗ[ℤ] (Fin n → ℤ)) := by
  first | exact @GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice | exact GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice | (intros; apply GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ptAlg_apply_of_left {R D E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]
    (z : Pt (SpAlg R D) E) (f : D →+* E) (h : z.left = spMap f) (a : D) : ptAlg z a = f a := by
  change (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom a = f a
  rw [h, Spec.preimage_map]
  rfl

end GlobalTheory.PtExt

theorem GlobalTheory.PtExt.bcPull_sumMul_fv : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R)) (B' : Over (Sp D)) (q : B'.left ⟶ (SpAlg R D ⊗ B).left) (w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D)) (π : B'.left ⟶ B.left), q ≫ (fst (SpAlg R D) B).left = B'.hom → q ≫ (snd (SpAlg R D) B).left = π → ∀ (mB : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 D) (B'.hom ≫ 𝟙 _) (algebraMap R D) π) (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))), bcPull w (sumMul d fun i ↦ fv (β i)) = fv (∑ i, d i • mB.coef.pullbackOneCocycle (β i)) := by
  classical
  intro R D _ _ _ B B' q w π hfst hsnd mB J _ d β
  have w' : π ≫ B.hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← hsnd, Category.assoc, Over.w (snd (SpAlg R D) B), w]
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  funext E i1 i2 E' i3 i4 ψ y
  have hzero : fv (0 : Z1 (O (dp0 D) (B'.hom ≫ 𝟙 _))) E E' ψ y = 0 := by
    have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd 0 0)
    simp only [add_zero, Fn1.add] at h
    linear_combination -h
  have hsum : ∀ s : Finset J, fv (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)) E E' ψ y =
      ∑ i ∈ s, algebraMap D E' (d i) * fv (mB.coef.pullbackOneCocycle (β i)) E E' ψ y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd (d j • mB.coef.pullbackOneCocycle (β j)) (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)))
      simp only [Fn1.add] at h
      rw [h, ih, hsmul]
  rw [hsum]
  simp only [bcPull, sumMul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback_changeOfBase R D (algebraMap R D) B B' π w' mB (β i)]
  congr 1
  · letI : Algebra R E := algVia (algebraMap R D) E
    have hl : (ptVia w y ≫ fst (SpAlg R D) B).left = spMap (algebraMap D E) := by
      rw [Over.comp_left]
      change (y.left ≫ q) ≫ (fst (SpAlg R D) B).left = _
      rw [Category.assoc, hfst]
      exact Over.w y
    rw [ptAlg_apply_of_left _ _ hl]
    exact ψ.commutes (d i)
  · simp only [bcPull]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    change (y.left ≫ q) ≫ (snd (SpAlg R D) B).left = y.left ≫ π
    rw [Category.assoc, hsnd]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.GaussBC

theorem two_le_coheight_of_chain {X : Scheme.{0}} {x e g : X} (h₁ : e ⤳ x) (h₂ : g ⤳ e) (n₁ : e ≠ x)
    (n₂ : g ≠ e) : (2 : ℕ∞) ≤ Order.coheight x := by
  have l₁ : x < e := lt_of_le_not_ge h₁ (fun h => n₁ (h₁.antisymm h).eq)
  have l₂ : e < g := lt_of_le_not_ge h₂ (fun h => n₂ (h₂.antisymm h).eq)
  have a₁ := Order.coheight_add_one_le l₁
  have a₂ := Order.coheight_add_one_le l₂
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight g + 1 + 1 := by gcongr; exact zero_le
    _ ≤ Order.coheight e + 1 := by gcongr
    _ ≤ Order.coheight x := a₁

theorem not_two_le_coheight_of_ringKrullDim_eq_one {X : Scheme.{0}} (x : X)
    (h : ringKrullDim (X.presheaf.stalk x) = 1) : ¬ (2 : ℕ∞) ≤ Order.coheight x := by
  intro h₂
  rw [ringKrullDim_stalk_eq_coheight] at h
  have : Order.coheight x = 1 := by exact_mod_cast h
  rw [this] at h₂
  exact absurd h₂ (by decide)

theorem apply_genericPoint_ne_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp R) [Flat f] : f (genericPoint X) ≠ closedPoint R := by
  intro h
  let p₀ : Sp R := ⟨⊥, Ideal.bot_prime⟩
  have hs : p₀ ⤳ f (genericPoint X) := by
    rw [h]; exact (PrimeSpectrum.le_iff_specializes p₀ (closedPoint R)).mp bot_le
  obtain ⟨w, hw, hfw⟩ := Flat.generalizingMap f hs
  have hw' : w = genericPoint X := (hw.antisymm (genericPoint_specializes w)).eq
  rw [hw', h] at hfw
  exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal hfw)

theorem apply_eq_of_closedFibre_dim_one : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → π y' = y := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hG hpb _ y y' hy hy' hdy hdy'
  haveI : Smooth H.hom := hG.smooth
  haveI : Flat H'.hom := MorphismProperty.of_isPullback hpb (inferInstanceAs (Flat H.hom))
  haveI : Flat (spMap a) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr ha
  haveI : Flat π := MorphismProperty.of_isPullback hpb.flip (inferInstanceAs (Flat (spMap a)))
  have hsq : ∀ z, H.hom (π z) = spMap a (H'.hom z) := fun z => by
    have := congrArg (fun f => f.base z) hpb.w
    simpa using this
  have hcl : spMap a (closedPoint D) = closedPoint T := by
    apply PrimeSpectrum.ext
    show Ideal.comap a (maximalIdeal D) = maximalIdeal T
    have hle : maximalIdeal T ≤ Ideal.comap a (maximalIdeal D) := Ideal.map_le_iff_le_comap.mp hm.le
    exact ((maximalIdeal.isMaximal T).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hback : ∀ p : Sp D, spMap a p = closedPoint T → p = closedPoint D := by
    intro p hp
    by_contra hne
    have hbot : p.asIdeal = ⊥ := by
      by_contra hb
      exact hne (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal hb)))
    have hker : Ideal.comap a ⊥ = maximalIdeal T := by
      rw [← hbot]; exact congrArg PrimeSpectrum.asIdeal hp
    apply IsDiscreteValuationRing.not_a_field D
    rw [← hm, ← hker]
    exact le_antisymm Ideal.map_comap_le bot_le
  set F : Set H.left := H.hom ⁻¹' {closedPoint T} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint T).preimage H.hom.continuous
  have hFi : IsIrreducible F := by
    haveI := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ H hG _ ((Sp T).fromSpecResidueField (closedPoint T))
    haveI : IrreducibleSpace (H.hom.fiber (closedPoint T)) := this
    have hr := (IrreducibleSpace.isIrreducible_univ (H.hom.fiber (closedPoint T))).image _
      (Scheme.Hom.fiberι H.hom (closedPoint T)).continuous.continuousOn
    rw [Set.image_univ] at hr
    convert hr using 1
    exact (Scheme.Hom.range_fiberι H.hom (closedPoint T)).symm
  have hξ₀ := hFi.isGenericPoint_genericPoint_closure
  rw [hFc.closure_eq] at hξ₀
  set ξ₀ := hFi.genericPoint
  have hgH := apply_genericPoint_ne_closedPoint H.hom
  have hgH' := apply_genericPoint_ne_closedPoint H'.hom
  have hyξ₀ : y = ξ₀ := by
    by_contra hne
    refine not_two_le_coheight_of_ringKrullDim_eq_one y hdy
      (two_le_coheight_of_chain (hξ₀.specializes hy) (genericPoint_specializes ξ₀) (Ne.symm hne) ?_)
    intro h; apply hgH; rw [h]; exact hξ₀.mem
  have hzξ₀ : π y' = ξ₀ := by
    by_contra hne
    have hz : π y' ∈ F := by
      show H.hom (π y') = closedPoint T
      rw [hsq, hy', hcl]
    obtain ⟨w, hw, hπw⟩ := Flat.generalizingMap π (hξ₀.specializes hz)
    refine not_two_le_coheight_of_ringKrullDim_eq_one y' hdy'
      (two_le_coheight_of_chain hw (genericPoint_specializes w) ?_ ?_)
    · rintro rfl; exact hne hπw
    · intro h; apply hgH'; apply hback; rw [← hsq, h, hπw]; exact hξ₀.mem
  rw [hzξ₀, hyξ₀]

end GlobalTheory.Desc.GaussBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFlagStalkSpan
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

theorem GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), colSpan (Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)).1 l = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellOpen ι N w) y hy (cellCol ι N w τ j)} := by
  intro ι _ N w τ l y hy
  unfold colSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.map_apply, cellCol, map_sum, GlobalTheory.QCoh.germ_smul,
    GlobalTheory.Twist.germ_resM, stalkStd, RingHom.comp_apply]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  refine Eq.congr_right (Finset.sum_congr rfl fun i _ => ?_)
  exact congrArg _ (VB.IsFrame.stalkBasis_apply _ _ _ _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupSubsingletonOfBoundedRamificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterGroup_subsingleton_of_bounded_ramification : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ U : Unif (maximalIdeal W) D Q H, GlobalTheory.LN.ToATotal U.toUnifPre → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (n N : ℕ), 2 ≤ n → (∀ j : ℕ, ∃ (T : Subring F) (_ : IsDiscreteValuationRing T) (g : W →+* T) (e : ℕ), (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ (∀ π, Irreducible π → ∃ ϖ : T, Irreducible ϖ ∧ Associated (g π) (ϖ ^ e)) ∧ ∀ σ : F ≃+* F, (∀ z ∈ T, σ z = z) → ∀ x : TF (R := W) F ⟶ H, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → Subsingleton D.toPre.X := by
  first | exact @GlobalTheory.TorsRam.subsingleton_of_bounded_ramification | exact GlobalTheory.TorsRam.subsingleton_of_bounded_ramification | (intros; apply GlobalTheory.TorsRam.subsingleton_of_bounded_ramification <;> assumption)
end

