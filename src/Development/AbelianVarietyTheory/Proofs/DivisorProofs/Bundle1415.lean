import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullstellensatzPointOfSystem
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry CategoryTheory

open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_rat_pt {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Sp K) [LocallyOfFiniteType f]
    {Z : Set X} (hZ : IsLocallyClosed Z) {x : X} (hx : x ∈ Z) :
    ∃ a : Sp K ⟶ X, a ≫ f = 𝟙 _ ∧ ∀ w, a w ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hZ
  replace hc : IsClosed {c} := hc
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp _ _ _, fun w => by rw [pointOfClosedPoint_apply]; exact hcZ⟩

theorem exists_pt_of_mem_cone : ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree → ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosure F K] (y : Fin S.N → K), y ≠ 0 → (∀ g ∈ S.imageIdeal, aeval y g = 0) → ∃ (x : S.Pt K) (c : K), c ≠ 0 ∧ S.coords x.1 = c • y := by
  intro F _ _ S hS hb K _ _ _ y hy hI
  haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed F
  classical
  by_contra hno
  push_neg at hno
  have hT : (S.baseChange K).IsVariety := hS.baseChange K
  have hbT : (S.baseChange K).BasePointFree := hb.baseChange K
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hy
  change y i₀ ≠ 0 at hi₀
  let u : Fin S.N → Fin S.N → K := fun j => y i₀ • Pi.single j 1 - y j • Pi.single i₀ 1
  have hu : ∀ (j : Fin S.N) (c : Fin S.N → K), ∑ l, u j l * c l = y i₀ * c j - y j * c i₀ := fun j c => by
    simp [u, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, mul_assoc]

  have hcov : ∀ z : (S.baseChange K).Y, ∃ j, z ∈ nonzeroLocus ((S.baseChange K).comb (u j)) := by
    by_contra hc
    push_neg at hc
    obtain ⟨z, hz⟩ := hc
    have := hT.smooth
    have : Smooth (S.baseChange K).str := SmoothOfRelativeDimension.smooth (S.baseChange K).D _
    have hZ : IsClosed (⋂ j, ((nonzeroLocus ((S.baseChange K).comb (u j)) : Set (S.baseChange K).Y)ᶜ)) :=
      isClosed_iInter fun j => (nonzeroLocus ((S.baseChange K).comb (u j))).isOpen.isClosed_compl
    obtain ⟨a, ha, haZ⟩ := GlobalTheory.ConeOnto.exists_rat_pt (S.baseChange K).str hZ.isLocallyClosed
      (x := z) (Set.mem_iInter.2 hz)
    let xa : (S.baseChange K).Pt K := ⟨a, ha.trans (Spec.map_id _).symm⟩
    have hbase : (S.baseChange K).baseHom a = RingHom.id K := LinSys.baseHom_ptOver xa
    have hv : ∀ j, y i₀ * (S.baseChange K).coords a j - y j * (S.baseChange K).coords a i₀ = 0 := fun j => by
      have h0 := Set.mem_iInter.1 (haZ (IsLocalRing.closedPoint K)) j
      have h1 : (S.baseChange K).val a ((S.baseChange K).comb (u j)) = 0 :=
        not_not.1 fun h => h0 (((S.baseChange K).val_ne_zero_iff a _).1 h)
      have h2 := ((S.baseChange K).val_comb a (u j)).symm.trans h1
      rw [hbase] at h2
      simp only [RingHom.id_apply] at h2
      exact (hu j ((S.baseChange K).coords a)).symm.trans h2
    have hc0 : (S.baseChange K).coords a i₀ ≠ 0 := fun h0 => hbT.coords_ne_zero a (funext fun j => by
      have := hv j
      rw [h0, mul_zero, sub_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hi₀)
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange K a
    refine hno (LinSys.toBase xa) (c⁻¹ * ((S.baseChange K).coords a i₀ / y i₀))
      (mul_ne_zero (inv_ne_zero hc) (div_ne_zero hc0 hi₀)) (funext fun j => ?_)
    have ej := congrFun e j
    have hvj := hv j
    change S.coords (a ≫ S.bcFst K) j = _
    simp only [Pi.smul_apply, smul_eq_mul] at ej ⊢
    have e1 : S.coords (a ≫ S.bcFst K) j = c⁻¹ * (S.baseChange K).coords a j := by
      rw [ej, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have e2 : (S.baseChange K).coords a j = (S.baseChange K).coords a i₀ / y i₀ * y j := by
      field_simp
      linear_combination hvj
    rw [e1, e2]
    ring

  have hX : (X i₀ : MvPolynomial (Fin (S.baseChange K).N) K).IsHomogeneous 1 := isHomogeneous_X K i₀
  obtain ⟨m, A, hA, hrel⟩ := GlobalTheory.SecIntegral.exists_integral_relation K (S.baseChange K) hT S.N 1 u
    ((S.baseChange K).form hX) hcov
  let σ : Fin S.N → MvPolynomial (Fin S.N) K := fun i => ∑ j, C (u i j) * X j
  have hσ : ∀ i, (σ i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C (Fin S.N) (u i j)).mul (isHomogeneous_X K j)
  let G : MvPolynomial (Fin S.N) K := X i₀ ^ m + ∑ k : Fin m, bind₁ σ (A k) * X i₀ ^ (k : ℕ)
  have hG : G.IsHomogeneous m := by
    refine (isHomogeneous_X_pow i₀ m).add (IsHomogeneous.sum _ _ _ fun k _ => ?_)
    have h1 : (bind₁ σ (A k)).IsHomogeneous (1 * (1 * (m - k))) :=
      (hA k).eval₂ C σ (fun r => isHomogeneous_C _ r) hσ
    have h2 := h1.mul (isHomogeneous_X_pow i₀ (k : ℕ))
    have e : 1 * (1 * (m - (k : ℕ))) + k = m := by omega
    rwa [e] at h2

  haveI := HeightExists.isIntegral hT
  obtain ⟨Ω, _, _, xg, hxg, -⟩ := HeightExists.exists_generic hT
  have hmem : G ∈ (S.baseChange K).imageIdeal := by
    rw [imageIdeal_eq_coneIdeal_of_generic K Ω _ xg hxg 1 _ one_ne_zero (one_smul _ _).symm]
    refine (mem_coneIdeal_of_isHomogeneous (K := K) (N := S.N) _ hG).2 ?_
    have h := hrel Ω xg
    rw [LinSys.powVal_form, LinSys.baseHom_ptOver] at h
    erw [eval₂_X] at h
    let cg : Fin S.N → Ω := (S.baseChange K).coords xg.1
    have h' : cg i₀ ^ m + ∑ k : Fin m, aeval (fun i : Fin S.N => ∑ j : Fin S.N, algebraMap K Ω (u i j) * cg j) (A k) *
        cg i₀ ^ (k : ℕ) = 0 := h
    show aeval cg G = 0
    simp only [G, σ, map_add, map_pow, map_sum, map_mul, aeval_X, aeval_bind₁, aeval_C]
    exact h'

  rw [← HeightExists.map_imageIdeal hS K] at hmem
  have hker : S.imageIdeal.map (MvPolynomial.map (algebraMap F K)) ≤ RingHom.ker (eval y) :=
    Ideal.map_le_iff_le_comap.2 fun g hg => by
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.eval_map, ← aeval_def]
      exact hI g hg
  have h0 : eval y G = 0 := hker hmem
  have hA0 : ∀ k : Fin m, eval y (bind₁ σ (A k)) = 0 := fun k => by
    show aeval y (bind₁ σ (A k)) = 0
    rw [aeval_bind₁]
    have e : (fun i => aeval y (σ i)) = 0 := funext fun i => by
      simp only [σ, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, Pi.zero_apply]
      rw [hu i y]
      ring
    rw [e, aeval_zero, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
    exact (hA k).coeff_eq_zero (d := 0) (by simp; omega)
  have h3 : eval y G = y i₀ ^ m := by
    simp only [G, map_add, map_pow, map_sum, map_mul, eval_X, hA0, zero_mul, Finset.sum_const_zero, add_zero]
  exact pow_ne_zero m hi₀ (h3.symm.trans h0)

end GlobalTheory.ConeOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivProdRenameSigmaOfNotMem
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

def polMapD (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) :
    (⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ) →ₗ[ℂ] MvPolynomial (Σ w, Λ w) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (Σ w, Λ w) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Sigma.mk w)).toLinearMap)

theorem polMapD_tprod (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (q : ∀ w, MvPolynomial (Λ w) ℂ) :
    polMapD W Λ (PiTensorProduct.tprod ℂ q) = ∏ v, MvPolynomial.rename (Sigma.mk v) (q v) := by
  simp [polMapD]

theorem polMapD_index_injective (W : Type) [Fintype W] (Λ : W → Type) :
    Function.Injective (fun f : ∀ w, (Λ w →₀ ℕ) => ∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) := by
  have key : ∀ (f : ∀ w, (Λ w →₀ ℕ)) (w : W) (l : Λ w),
      (∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) ⟨w, l⟩ = f w l := by
    intro f w l
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply sigma_mk_injective _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Sigma.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (Σ w, Λ w) →₀ ℕ => F ⟨w, l⟩) h

theorem polMapD_tprod_monomial (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (f : ∀ w, (Λ w →₀ ℕ)) :
    polMapD W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial (Λ w) ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMapD, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

theorem polMapD_injective (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) :
    Function.Injective (polMapD W Λ) := by
  let B := Basis.piTensorProduct (fun w : W => basisMonomials (Λ w) ℂ)
  have hli : LinearIndependent ℂ (polMapD W Λ ∘ B) := by
    have h := (basisMonomials (Σ w, Λ w) ℂ).linearIndependent.comp _ (polMapD_index_injective W Λ)
    have e : polMapD W Λ ∘ B = (basisMonomials (Σ w, Λ w) ℂ) ∘
        (fun f : ∀ w, (Λ w →₀ ℕ) => ∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMapD_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMapD W Λ ∘ₗ Finsupp.linearCombination ℂ B =
      Finsupp.linearCombination ℂ (polMapD W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

theorem atPl_tprod_dep {W : Type} [Fintype W] [DecidableEq W] {Λ : W → Type} (w : W)
    (L : Module.End ℂ (MvPolynomial (Λ w) ℂ)) (p : ∀ v, MvPolynomial (Λ v) ℂ) :
    atPl (V := fun w => MvPolynomial (Λ w) ℂ) w L (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (L (p w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext v
  by_cases hv : v = w
  · subst hv; simp
  · simp [Function.update_of_ne hv]

theorem polMapD_atPl_mulLeft_X (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (w : W) (l : Λ w) :
    polMapD W Λ ∘ₗ atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X ⟨w, l⟩) ∘ₗ polMapD W Λ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, atPl_tprod_dep, polMapD_tprod,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Sigma.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

theorem pderiv_rename_sigmaMk_of_ne {W : Type} {Λ : W → Type} {v w : W} (h : v ≠ w) (l : Λ w)
    (r : MvPolynomial (Λ v) ℂ) :
    MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w) (MvPolynomial.rename (Sigma.mk v) r) = 0 := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e; exact h (congrArg Sigma.fst e)

theorem pderiv_prod_rename_sigma_of_notMem {W : Type} {Λ : W → Type} {w : W} (l : Λ w)
    (q : ∀ v, MvPolynomial (Λ v) ℂ) (s : Finset W) (hs : w ∉ s) :
    MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w) (∏ v ∈ s, MvPolynomial.rename (Sigma.mk v) (q v)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hs.2,
      pderiv_rename_sigmaMk_of_ne (fun e => hs.1 e.symm)]
    simp

theorem polMapD_atPl_pderiv (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (w : W) (l : Λ w) :
    polMapD W Λ ∘ₗ atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w)).toLinearMap ∘ₗ polMapD W Λ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro q
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, atPl_tprod_dep, polMapD_tprod]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Sigma.mk i)
      (Function.update q w ((MvPolynomial.pderiv l).toLinearMap (q w)) i) =
      ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Sigma.mk i) (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [h1, Function.update_self, Derivation.coeFn_coe, Derivation.coeFn_coe, Derivation.leibniz,
    pderiv_prod_rename_sigma_of_notMem l q _ (Finset.notMem_erase w _),
    MvPolynomial.pderiv_rename sigma_mk_injective l (q w)]
  simp [mul_comm]

theorem exists_polMapD : ∀ (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type),
    ∃ θ : (⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ) →ₗ[ℂ] MvPolynomial (Σ w, Λ w) ℂ, Function.Injective θ ∧
      ∀ (w : W) (l : Λ w) (T : ⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ),
        θ (atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T) =
            MvPolynomial.X ⟨w, l⟩ * θ T ∧
          θ (atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (MvPolynomial.pderiv l).toLinearMap T) =
            MvPolynomial.pderiv ⟨w, l⟩ (θ T) := by
  intro W _ _ Λ
  refine ⟨polMapD W Λ, polMapD_injective W Λ, fun w l T => ⟨?_, ?_⟩⟩
  · exact LinearMap.congr_fun (polMapD_atPl_mulLeft_X W Λ w l) T
  · exact LinearMap.congr_fun (polMapD_atPl_pderiv W Λ w l) T

end GlobalTheory.CCRFock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInertStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
theorem _root_.GlobalTheory.T.place_split_or_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  first | exact @GlobalTheory.KFinLoc.split_or_inert | exact GlobalTheory.KFinLoc.split_or_inert | (intros; apply GlobalTheory.KFinLoc.split_or_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusCone
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConeMax

theorem prod_max_le_prod (r m e : ℕ) (c : ℝ) (hc : 0 < c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c,
    ∏ k : Fin r ⊕ Fin r ⊕ Fin m, max 1 (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ))) k) ^ e ≤
      C * ∏ i, t i ^ e := by
  set c0 : ℝ := min c 1 ^ r with hc0
  have hm0 : 0 < min c 1 := lt_min hc one_pos
  have hc0pos : 0 < c0 := pow_pos hm0 r
  have hc0le : c0 ≤ 1 := pow_le_one₀ hm0.le (min_le_right _ _)
  refine ⟨(c0⁻¹ ^ e) ^ r * (c0⁻¹ ^ e) ^ r, by positivity, ?_⟩
  intro t ht
  have hlow : ∀ i, c0 ≤ t i := fun i => GlobalTheory.LatCount.cone_pow_le hc ht i
  have htpos : ∀ i, 0 < t i := fun i => hc0pos.trans_le (hlow i)
  have h1 : ∀ i, max 1 (t i) ≤ t i * c0⁻¹ := by
    intro i
    have hi : 1 ≤ c0⁻¹ := one_le_inv₀ hc0pos |>.2 hc0le
    refine max_le ?_ ?_
    · rw [← mul_inv_cancel₀ hc0pos.ne']
      exact mul_le_mul_of_nonneg_right (hlow i) (inv_nonneg.2 hc0pos.le)
    · exact le_mul_of_one_le_right (htpos i).le hi
  have h2 : ∀ i, max 1 (t i)⁻¹ ≤ c0⁻¹ := by
    intro i
    refine max_le (one_le_inv₀ hc0pos |>.2 hc0le) ?_
    exact inv_anti₀ hc0pos (hlow i)
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, max_self, one_pow, Finset.prod_const_one, mul_one]
  have A : ∏ i : Fin r, max 1 (t i) ^ e ≤ ∏ i : Fin r, (t i ^ e * c0⁻¹ ^ e) := by
    refine Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (le_max_left _ _ |>.trans' zero_le_one) (h1 i) e
  have B : ∏ i : Fin r, max 1 (t i)⁻¹ ^ e ≤ ∏ _i : Fin r, c0⁻¹ ^ e :=
    Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun i _ =>
      pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (h2 i) e
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at A
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at B
  have hA0 : 0 ≤ ∏ i : Fin r, max 1 (t i)⁻¹ ^ e := Finset.prod_nonneg fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  calc (∏ i : Fin r, max 1 (t i) ^ e) * ∏ i : Fin r, max 1 (t i)⁻¹ ^ e
      ≤ ((∏ i : Fin r, t i ^ e) * (c0⁻¹ ^ e) ^ r) * (c0⁻¹ ^ e) ^ r :=
        mul_le_mul A B hA0
          (mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (htpos i).le _) (by positivity))
    _ = (c0⁻¹ ^ e) ^ r * (c0⁻¹ ^ e) ^ r * ∏ i, t i ^ e := by ring

end GlobalTheory.ConeMax
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsGlobalResiduesStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productOfVectorMultiplications_global_residues : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (t j : ℕ) (u : Fin t → Fin G.N → K), ∀ x ∈ G.global j, ∃ x' ∈ G.global (j + t), word (shift G) u (Pi.single j x) = Pi.single (j + t) x' ∧ ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s) (δ : ℕ) (Co : Coord G hs δ) (p : Fin δ), Co.ev (j + t) (hs.res (j + t) x') p = (∏ q, ∑ k, u q k * Co.y p k) * Co.ev j (hs.res j x) p := by
  first | exact @GlobalTheory.HSShort.GlobWord.word_global | exact GlobalTheory.HSShort.GlobWord.word_global | (intros; apply GlobalTheory.HSShort.GlobWord.word_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuantumDetCentralCoeffsConjStatement
section
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_central_coeffs_conj : ∀ (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A), IsLieRep ρ → ∀ P P' : Matrix (Fin n) (Fin n) ℂ, P * P' = 1 → ∃ c : ℕ → A, c n = 1 ∧ (∀ k ≤ n, c k ∈ invAlg ρ) ∧ ∀ u : ℂ, Formalism.REAL.qdet (fun a b => ρ (P * Matrix.single a b 1 * P')) u = ∑ k ∈ Finset.range (n + 1), u ^ k • c k := by
  first | exact @GlobalTheory.qdet_frame_coeff_mem_invAlg | exact GlobalTheory.qdet_frame_coeff_mem_invAlg | (intros; apply GlobalTheory.qdet_frame_coeff_mem_invAlg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientIntegralRowReduction
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem exists_KO_row_zero_of_rank_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (X : Matrix A D k) (hX : X.rank < Fintype.card A) :
    ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by

  have hdep : ¬ LinearIndependent k X.row := by
    intro h
    rw [linearIndependent_iff_card_eq_finrank_span] at h
    rw [rank_eq_finrank_span_row] at hX
    exact (lt_irrefl _) (h ▸ hX)
  obtain ⟨c, hc, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hcj : ∀ j, ∑ i, c i * X i j = 0 := by
    intro j
    have := congrFun hc j
    simpa [Finset.sum_apply, Matrix.row] using this

  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (c i))
    ⟨i₁, Finset.mem_univ _⟩
  have hc0 : c i₀ ≠ 0 := by
    intro h0
    have := hmax i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₁ this
  set c' : A → k := fun i => c i / c i₀ with hc'
  have hc'int : ∀ i, c' i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff, hc', map_div₀]
    have hpos : 0 < valuation k (c i₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hc0
    exact (div_le_one₀ hpos).2 (hmax i (Finset.mem_univ _))
  have hc'0 : c' i₀ = 1 := div_self hc0

  let E : Matrix A A k := Matrix.of fun i j => if i = i₀ ∧ j ≠ i₀ then c' j else 0
  have hEE : E * E = 0 := by
    ext i j
    simp only [Matrix.mul_apply, E, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = i₀
    · simp [hl]
    · simp [hl]
  have hEint : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [E, Matrix.of_apply]
    split_ifs
    · exact hc'int j
    · exact zero_mem _
  have h1int : ∀ i j, (1 : Matrix A A k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  let g : GL A k := ⟨1 + E, 1 - E, by rw [add_mul, one_mul, mul_sub, mul_one, hEE]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hEE]; abel⟩
  refine ⟨g, ?_, i₀, fun j => ?_⟩
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      exact add_mem (h1int i j) (hEint i j)
    · show (1 - E) i j ∈ 𝒪[k]
      exact sub_mem (h1int i j) (hEint i j)
  · show (((1 : Matrix A A k) + E) * X) i₀ j = 0
    have hrow : ∀ l, (1 + E) i₀ l = c' l := by
      intro l
      by_cases hl : l = i₀
      · subst hl; simp [E, hc'0]
      · simp [E, hl, Matrix.one_apply, Ne.symm hl]
    rw [Matrix.mul_apply]
    simp_rw [hrow, hc', div_mul_eq_mul_div, ← Finset.sum_div, hcj j, zero_div]

end GlobalTheory.RankCoinv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsRestrictionSmoothRightDerivEqStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPointsRestriction_smooth_rightDeriv_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ φ : Sm E a, ∀ x, (glH E a).IsSmoothFun (glRes φ.1 x) ∧ ∀ X : glL E a, (glH E a).rightDeriv X (glRes φ.1 x) = glRes (lie E a (toL X.1) φ).1 x := by
  first | exact @GlobalTheory.HCA.glRes_smooth_rightDeriv | exact GlobalTheory.HCA.glRes_smooth_rightDeriv | (intros; apply GlobalTheory.HCA.glRes_smooth_rightDeriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlaceStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ (u : Matrix α β (AE F E)) (r : ℝ) (w : InfinitePlace F),
      (realAd F r • u).map (piInf (τ w)) = (r : ℂ) • u.map (piInf (τ w)) := by
  first | exact @GlobalTheory.RealScalar.realAd_smul_map | exact GlobalTheory.RealScalar.realAd_smul_map | (intros; apply GlobalTheory.RealScalar.realAd_smul_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectorsStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakExponential_action_on_fockVectors : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := by
  first | exact @GlobalTheory.ExpAct.expAct_fock | exact GlobalTheory.ExpAct.expAct_fock | (intros; apply GlobalTheory.ExpAct.expAct_fock <;> assumption)
end

