import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySquareZeroSmoothLiftSystemOfIsFun
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem rho_id_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀}
    {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀} (L : Pre I π F) (hL : L.IsFun) (T : C) (y : L.B T) :
    L.ρ (𝟙 T) y = y := by
  set e := L.ρ (𝟙 T) with he
  have idem : ∀ x, e (e x) = e x := fun x ↦ by
    have := hL (𝟙 T) (𝟙 T) x
    rw [Category.comp_id] at this
    exact this.symm
  have hJ := LiftSys.map_sq hI (L.B T)
  have memJ : ∀ x, x - e x ∈ I.map (algebraMap R (L.B T)) := fun x ↦ by
    rw [← L.ker]
    rw [map_sub, L.nat, mp_id, sub_self]
  have sq0 : ∀ u v, u ∈ I.map (algebraMap R (L.B T)) → v ∈ I.map (algebraMap R (L.B T)) → u * v = 0 := by
    intro u v hu hv
    have : u * v ∈ I.map (algebraMap R (L.B T)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hu hv
    rw [hJ] at this
    simpa using this
  have fix : ∀ z ∈ I.map (algebraMap R (L.B T)), e z = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, -, rfl⟩ := hx
      exact e.commutes i
    | zero => exact map_zero e
    | add x w _ _ hx hw => rw [map_add, hx, hw]
    | smul b x hxm hx =>
      rw [smul_eq_mul, map_mul, hx]
      have := sq0 _ _ (memJ b) hxm
      rw [sub_mul] at this
      exact (sub_eq_zero.1 this).symm
  have h1 := fix _ (memJ y)
  rw [map_sub, idem, sub_self] at h1
  exact (sub_eq_zero.1 h1.symm).symm

theorem nonempty_sys_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ L hL
  exact ⟨{
    F := {
      obj := L.B
      map := fun a ↦ CommAlgCat.ofHom (L.ρ a)
      map_id := fun T ↦ CommAlgCat.hom_ext (AlgHom.ext fun y ↦ rho_id_eq hI L hL T y)
      map_comp := fun a b ↦ CommAlgCat.hom_ext (AlgHom.ext fun x ↦ hL a b x) }
    p := L.p
    semi := L.semi
    nat := fun a b ↦ L.nat a b
    surj := L.surj
    ker := L.ker
    smooth := L.smooth }⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealMapCompleteDvrEqProdLifts
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

open MvPolynomial in

theorem GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ → ∀ (J : Ideal B)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ψ : Fin (Module.finrank K L) → (B →+* V')), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ (∀ j, (ψ j).comp φ = f.comp h) ∧
      (GlobalTheory.NormSheaf.normIdeal A K L B J).map (f.comp h) = ∏ j, J.map (ψ j) := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ hcomp J V _ _ _ _ hV h
  obtain ⟨R, _, _, hinj, hfin, σ, hσ, hP⟩ := GlobalTheory.T.exists_finite_algebra_splitting_normForm A B K L φ hφ hcomp
  obtain ⟨V', _, _, _, _, f, ρ, hV', hf, hloc, hρ⟩ := GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' A R hinj hfin V hV h
  let ψ : Fin (Module.finrank K L) → (B →+* V') := fun j => ρ.comp (σ j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hloc, ?_, ?_⟩
  · intro j
    show (ρ.comp (σ j)).comp φ = f.comp h
    rw [RingHom.comp_assoc, hσ j, hρ]
  have key : ∀ (m : ℕ) (g : Fin m → B) (P : MvPolynomial (Fin m) A),
      P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i →
      Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) =
        ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by
    intro m g P hPR
    rw [← GlobalTheory.T.span_coeff_prod_linear_eq_prod_span V' _ m (fun j i => ψ j (g i))]
    have hE : (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V') = (P.map (algebraMap A R)).map ρ := by
      rw [hPR]; simp [map_prod, map_sum, ψ]
    have hfun : (fun s => (f.comp h) (P.coeff s)) =
        fun s => (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V').coeff s := by
      funext s
      rw [hE, MvPolynomial.map_map, MvPolynomial.coeff_map, hρ]
    rw [hfun]
  unfold GlobalTheory.NormSheaf.normIdeal
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨a, ⟨m, g, hgJ, s, hs⟩, rfl⟩
    obtain ⟨P, hPK, hPR⟩ := hP m g
    have ha : a = P.coeff s := IsFractionRing.injective A K (by rw [hs, ← hPK, MvPolynomial.coeff_map])
    have hmem : (f.comp h) a ∈ Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) :=
      Ideal.subset_span ⟨s, by rw [ha]⟩
    rw [key m g P hPR] at hmem
    have hle : ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) ≤ ∏ j, J.map (ψ j) :=
      Finset.prod_le_prod' (fun j _ => Ideal.span_le.2 (by
        rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)))
    exact hle hmem
  · have hfg : ∀ j, ∃ t : Finset V', (↑t : Set V') ⊆ ψ j '' (J : Set B) ∧ J.map (ψ j) = Ideal.span (↑t : Set V') := by
      intro j
      have h1 : (J.map (ψ j)).FG := IsNoetherian.noetherian _
      rw [Ideal.map] at h1 ⊢
      exact (Submodule.fg_span_iff_fg_span_finset_subset _).1 h1
    choose t ht hspan using hfg
    have hpre : ∀ (x : Σ j, (t j : Set V')), ∃ b ∈ J, ψ x.1 b = x.2 := by
      rintro ⟨j, x, hx⟩
      obtain ⟨b, hb, e⟩ := ht j hx
      exact ⟨b, hb, e⟩
    choose pre hpreJ hpreψ using hpre
    let e := Fintype.equivFin (Σ j, (t j : Set V'))
    let g : Fin (Fintype.card (Σ j, (t j : Set V'))) → B := fun i => pre (e.symm i)
    have hgJ : ∀ i, g i ∈ J := fun i => hpreJ _
    obtain ⟨P, hPK, hPR⟩ := hP _ g
    have hj : ∀ j, Ideal.span (Set.range fun i => ψ j (g i)) = J.map (ψ j) := by
      intro j
      apply le_antisymm
      · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)
      · rw [hspan j, Ideal.span_le]
        intro x hx
        apply Ideal.subset_span
        refine ⟨e ⟨j, x, hx⟩, ?_⟩
        simp only [g, Equiv.symm_apply_apply]
        exact hpreψ ⟨j, x, hx⟩
    calc ∏ j, J.map (ψ j) = ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by simp_rw [hj]
      _ = Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) := (key _ g P hPR).symm
      _ ≤ _ := by
        rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        apply Ideal.subset_span
        exact ⟨P.coeff s, ⟨_, g, hgJ, s, by rw [← hPK, MvPolynomial.coeff_map]⟩, rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSkewHermitianBasisVectorEqSqrtTwo
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem boxEnt_norm_sq_eq {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b : Fin r)
    (hab : (a, b) ≠ (z, z)) :
    ∃ P Q : Fin r × Fin r, P ≠ Q ∧ ∀ p : Fin r × Fin r,
      ‖boxEnt d z a b p.1 p.2‖ ^ 2 = (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
  have hdd : ‖((d a * d b : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rcases hd a with h | h <;> rcases hd b with h' | h' <;> simp [h, h']
  rcases lt_trichotomy a b with h | h | h
  · refine ⟨(a, b), (b, a), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)
  · subst h
    have haz : a ≠ z := fun e => hab (by rw [e])
    refine ⟨(a, a), (z, z), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact haz e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, lt_irrefl, if_false, Prod.mk.injEq]
      split_ifs <;> simp_all
  · refine ⟨(b, a), (a, b), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_neg (not_lt.2 h.le), if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)

theorem norm_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, ‖boxVec d z k‖ = √2 := by
  intro E _ _ _ r Ψ d z hd k
  obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
  obtain ⟨P, Q, hPQ, hPn⟩ := boxEnt_norm_sq_eq (d τ) (hd τ) z a b hab
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · have : ∀ p : Fin r × Fin r, ‖(boxVec d z ⟨τ, ⟨(a, b), hab⟩⟩) (τ, p)‖ ^ 2 =
        (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
      intro p
      rw [← hPn p]
      simp [boxVec]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    norm_num
  · intro τ' _ hτ'
    apply Finset.sum_eq_zero
    intro p _
    simp [boxVec, hτ']
  · simp

end GlobalTheory.CovTop.VolUp.FrameBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalFibresCharUnit
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreRing

variable (R A K : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A] [Algebra R K]
  (hR : ∀ f g : R →+* A ⊗[ℤ] K, f = g)

def inclK : K →ₐ[R] A ⊗[ℤ] K :=
  { (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := K)).toRingHom with
    commutes' := fun r => by
      have h : ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := K)).toRingHom.comp (algebraMap R K)) =
          algebraMap R (A ⊗[ℤ] K) :=
        hR _ _
      exact RingHom.congr_fun h r }

def toR : A ⊗[ℤ] K →+* A ⊗[R] K :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := K)).toIntAlgHom
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K)).toRingHom.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

def ofR : A ⊗[R] K →+* A ⊗[ℤ] K :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (R := ℤ) (S := R) (A := A) (B := K))
    (inclK R A K hR) (fun _ _ => Commute.all _ _)).toRingHom

lemma toR_tmul (a : A) (k : K) : toR R A K (a ⊗ₜ[ℤ] k) = a ⊗ₜ[R] k := by
  simp [toR, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

lemma ofR_tmul (a : A) (k : K) : ofR R A K hR (a ⊗ₜ[R] k) = a ⊗ₜ[ℤ] k := by
  simp [ofR, inclK, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

def tensorIntEquiv : A ⊗[ℤ] K ≃+* A ⊗[R] K :=
  RingEquiv.ofRingHom (toR R A K) (ofR R A K hR)
    (by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a k => simp [ofR_tmul, toR_tmul]
      | add x y hx hy => simp only [map_add, RingHom.comp_apply, RingHom.id_apply] at hx hy ⊢; rw [hx, hy])
    (by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a k => simp [ofR_tmul, toR_tmul]
      | add x y hx hy => simp only [map_add, RingHom.comp_apply, RingHom.id_apply] at hx hy ⊢; rw [hx, hy])

lemma tensorIntEquiv_tmul (a : A) (k : K) : tensorIntEquiv R A K hR (a ⊗ₜ[ℤ] k) = a ⊗ₜ[R] k := toR_tmul R A K a k

end GlobalTheory.FibreRing

namespace GlobalTheory.RealMult

theorem fibre_tensor_reduced_minimalPrimes : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (V : M.Opens),
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
      pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) →
    ∀ (K : Type) [Field K], (N : K) ≠ 0 → ∀ (W : M.Opens) (hW : IsAffineOpen W),
      IsReduced (Γ(M, W) ⊗[ℤ] K) ∧ ∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
        hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V := by
  intro N M s V hnorm hcodim K _ hNK W hW
  classical
  have hu : IsUnit (Int.castRingHom K (N : ℤ)) := by
    rw [isUnit_iff_ne_zero]; simpa using hNK
  let φ : Localization.Away (N : ℤ) →+* K := IsLocalization.Away.lift (N : ℤ) hu
  letI : Algebra (Localization.Away (N : ℤ)) K := φ.toAlgebra
  let t : Sp K ⟶ Sp (Localization.Away (N : ℤ)) := spMap φ
  have H : IsPullback (pullback.fst s t) (pullback.snd s t) s
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (N : ℤ)) K))) :=
    IsPullback.of_hasPullback s t
  letI : Algebra (Localization.Away (N : ℤ)) Γ(M, W) := (DVR.FlatBC.algX s W).toAlgebra
  let U' := pullback.fst s t ⁻¹ᵁ W ⊓ pullback.snd s t ⁻¹ᵁ ⊤
  let E : Γ(M, W) ⊗[ℤ] K ≃+* Γ(pullback s t, U') :=
    (GlobalTheory.FibreRing.tensorIntEquiv (Localization.Away (N : ℤ)) Γ(M, W) K
      (fun f g => IsLocalization.ringHom_ext (Submonoid.powers (N : ℤ)) (RingHom.ext_int _ _))).trans
      (DVR.FlatBC.eTens s (pullback.snd s t) (pullback.fst s t) H W hW)
  have hE : ∀ a, E (a ⊗ₜ[ℤ] 1) = ((pullback.fst s t).appLE W U' inf_le_left).hom a := by
    intro a
    simp only [E, RingEquiv.trans_apply, GlobalTheory.FibreRing.tensorIntEquiv_tmul]
    erw [DVR.FlatBC.eTens_tmul]
    rw [map_one, _root_.mul_one]
  have hU' : IsAffineOpen U' := by
    have e : U' = pullback.fst s t ⁻¹ᵁ W := by simp [U']
    rw [e]
    haveI : IsAffineHom (pullback.fst s t) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback s t).flip inferInstance
    exact hW.preimage _
  have hst := hnorm K t
  haveI : ∀ y : ↥(pullback s t), _root_.IsReduced ((pullback s t).presheaf.stalk y) := fun y => by
    haveI := (hst y).1; infer_instance
  haveI : IsReduced (pullback s t) := isReduced_of_isReduced_stalk _
  refine ⟨isReduced_of_injective E.toRingHom E.injective, ?_⟩
  intro q hq
  haveI : q.IsPrime := hq.1.1
  let q' : Ideal Γ(pullback s t, U') := q.comap E.symm.toRingHom
  haveI hq'p : q'.IsPrime := Ideal.comap_isPrime _ _
  have hq' : q' ∈ minimalPrimes Γ(pullback s t, U') := by
    refine ⟨⟨hq'p, bot_le⟩, fun p hp hle => ?_⟩
    haveI : p.IsPrime := hp.1
    have h1 : p.comap E.toRingHom ≤ q := by
      intro x hx
      have := hle hx
      simpa [q'] using this
    have h2 := hq.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ h1
    intro x hx
    have h3 : E.symm x ∈ p.comap E.toRingHom := h2 hx
    rw [Ideal.mem_comap] at h3
    simpa using h3
  let y' : PrimeSpectrum Γ(pullback s t, U') := ⟨q', hq'p⟩
  have hmem : hU'.fromSpec y' ∈ U' := by
    have h := hU'.range_fromSpec
    show hU'.fromSpec y' ∈ (U' : Set ↥(pullback s t))
    rw [← h]; exact ⟨y', rfl⟩
  letI algSt : Algebra Γ(pullback s t, U') ((pullback s t).presheaf.stalk (hU'.fromSpec y')) :=
    TopCat.Presheaf.algebra_section_stalk (pullback s t).presheaf ⟨hU'.fromSpec y', hmem⟩
  have hst' := hU'.isLocalization_stalk' y' hmem
  have hd := @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q' _
    ((pullback s t).presheaf.stalk (hU'.fromSpec y')) _ algSt hst'
  have hdim : ringKrullDim ((pullback s t).presheaf.stalk (hU'.fromSpec y')) = 0 := by
    rw [hd,
      Ideal.height_eq_zero_iff.mpr hq']
    rfl
  have hV : pullback.fst s t (hU'.fromSpec y') ∈ V := by
    by_contra hn
    have := hcodim K t _ hn
    rw [hdim] at this
    exact absurd this (by decide)
  have e := IsAffineOpen.SpecMap_appLE_fromSpec (pullback.fst s t) hW hU' inf_le_left
  have hpt : pullback.fst s t (hU'.fromSpec y') =
      hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K))
        ⟨q, hq.1.1⟩) := by
    change (hU'.fromSpec ≫ pullback.fst s t) y' = _
    rw [← e]
    change hW.fromSpec ((Spec.map ((pullback.fst s t).appLE W U' inf_le_left)) y') = _
    congr 1
    apply PrimeSpectrum.ext
    ext x
    show x ∈ Ideal.comap ((pullback.fst s t).appLE W U' inf_le_left).hom q' ↔ _
    simp only [Ideal.mem_comap, q', PrimeSpectrum.comap_asIdeal]
    rw [← hE]
    simp
  rw [← hpt]; exact hV

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.BdDim

def TrLe (K : Type) [Field K] (n : ℕ) : Prop := Algebra.trdeg (⊥ : Subfield K) K ≤ n

theorem TrLe.mono {K : Type} [Field K] {n m : ℕ} (h : TrLe K n) (hnm : n ≤ m) : TrLe K m :=
  le_trans h (by exact_mod_cast hnm)

theorem TrLe.of_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (h : TrLe L n) : TrLe K n := by
  have hb : ∀ x : (⊥ : Subfield K), f x ∈ (⊥ : Subfield L) := fun x =>
    (show (⊥ : Subfield K) ≤ (⊥ : Subfield L).comap f from bot_le) x.2
  let e : (⊥ : Subfield K) →+* (⊥ : Subfield L) := (f.comp (Subfield.subtype _)).codRestrict _ hb
  have he : Function.Surjective e := fun y => by
    have : (⊥ : Subfield L) ≤ (⊥ : Subfield K).map f := bot_le
    obtain ⟨x, hx, hxy⟩ := this y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (⊥ : Subfield K) K
  refine le_trans ?_ h
  rw [← hs.cardinalMk_eq_trdeg]
  have := hs.1.ringHom_of_comp_eq e f he f.injective (RingHom.ext fun _ => rfl)
  exact this.cardinalMk_le_trdeg

example : TrLe ℚ 0 := by
  have : Algebra.IsAlgebraic (⊥ : Subfield ℚ) ℚ := ⟨fun x => isAlgebraic_algebraMap (⟨x, by simpa using SubfieldClass.ratCast_mem (⊥ : Subfield ℚ) x⟩ : (⊥ : Subfield ℚ))⟩
  simp [TrLe, trdeg_eq_zero]

section Fibres

variable {T X Y Z : Scheme.{0}}

def SameFibre (G : Over X) [GrpObj G] (x : T ⟶ X) (G' : Over Y) [GrpObj G'] (y : T ⟶ Y) : Prop :=
  ∃ (A : Over T) (_ : GrpObj A) (φ : A.left ⟶ G.left) (ψ : A.left ⟶ G'.left),
    IsGrpPullback A G x φ ∧ IsGrpPullback A G' y ψ

def IsAbPart {k : Type} [Field k] (G : Over X) [GrpObj G] (x : Sp k ⟶ X) (B : Over Y) [GrpObj B] (y : Sp k ⟶ Y) : Prop :=
  ∃ (A : Over (Sp k)) (_ : GrpObj A) (φ : A.left ⟶ G.left) (t : TorusExtension A) (β : t.B.left ⟶ B.left),
    IsGrpPullback A G x φ ∧ @IsGrpPullback _ _ t.B t.grpB B _ y β

theorem SameFibre.refl (G : Over X) [GrpObj G] (x : T ⟶ X) : SameFibre G x G x :=
  ⟨_, _, _, _, isGrpPullback_pullback G x, isGrpPullback_pullback G x⟩

theorem IsAbPart.trans {k : Type} [Field k] {G : Over X} [GrpObj G] {x : Sp k ⟶ X} {B : Over Y} [GrpObj B] {y : Sp k ⟶ Y}
    {B' : Over Z} [GrpObj B'] {z : Sp k ⟶ Z} (h : IsAbPart G x B y) (h' : SameFibre B y B' z) : IsAbPart G x B' z := by
  obtain ⟨A, _, φ, t, β, h₁, h₂⟩ := h
  obtain ⟨C, _, ψ, ψ', h₃, h₄⟩ := h'
  letI := t.grpB
  obtain ⟨e, he, -⟩ := grpPullback_iso h₂ h₃
  exact ⟨A, _, φ, t, _, h₁, ((isGrpPullback_of_iso e).comp h₄).congr (Category.id_comp _) rfl⟩

theorem IsAbPart.comp {k : Type} [Field k] {G : Over X} [GrpObj G] {x : Sp k ⟶ X} {B : Over Y} [GrpObj B] {y : Sp k ⟶ Y}
    {G' : Over Z} [GrpObj G'] {f : X ⟶ Z} {φ : G.left ⟶ G'.left} (h : IsAbPart G x B y) (h' : IsGrpPullback G G' f φ) :
    IsAbPart G' (x ≫ f) B y := by
  obtain ⟨A, _, φ, t, β, h₁, h₂⟩ := h
  exact ⟨A, _, _, t, β, h₁.comp h', h₂⟩

end Fibres

end GlobalTheory.BdDim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllTuplesOverCoreOfRankBound
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core_of_size :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRowR T R κ v₀ O ph i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hC hoff hused hT hI i hP hph
  have hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  have h0 : OneMapRow0 T R κ v₀ O i :=
    GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hci D G Pl0 T0 A T R F κ v₀ hC (GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields D G Pl0 T0 A T R κ v₀ hT) hI O i hP
  exact GlobalTheory.T.oneMapRow_all_tuples_of_core_clauses hci D G Pl0 T0 A T R F κ v₀ O ph hC hoff hused hT hI i hP hph
    (GlobalTheory.T.classSums_span_cuspForms_baseTuple_second_field D G Pl0 T0 A T R F κ v₀ O hn hC hT hI i hP h0)

end GlobalTheory.OneMapCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenAffineIntegrallyClosedDomainStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_affine_integrally_closed_domain : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → Nonempty (Sp A) → ∃ (_ : IsDomain A) (_ : IsIntegrallyClosed A) (_ : Algebra V A) (_ : Algebra.FiniteType V A), Function.Injective (algebraMap V A) ∧ ∃ e : A, e ≠ 0 ∧ ∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → IsTest p Xw (spMap (kO.comp φ) ≫ w) := by
  first | exact @GlobalTheory.FlatModel.chart_normal_domain_testPoints | exact GlobalTheory.FlatModel.chart_normal_domain_testPoints | (intros; apply GlobalTheory.FlatModel.chart_normal_domain_testPoints <;> assumption)
end
end

