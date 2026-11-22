import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicity
section
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DetMonotone

private theorem exists_unitary_diagonal_eigenvalues_of_isHermitian {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix κ κ ℂ, U * star U = 1 ∧ star U * U = 1 ∧
      A = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
  refine ⟨(hA.eigenvectorUnitary : Matrix κ κ ℂ), Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, ?_⟩
  conv_lhs => rw [hA.spectral_theorem]
  rfl

theorem detMono : DetMono := by
  open ComplexOrder in (
    have one_le_re_det_lemma_2 : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] {Q : Matrix κ κ ℂ},
        Q.PosSemidef → 1 ≤ ((1 + Q).det).re := by
      intro κ _ _ Q hQ
      obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hQ.1
      have hsum : 1 + Q = U * diagonal (fun i => 1 + (hQ.1.eigenvalues i : ℂ)) * star U := by
        conv_lhs => rw [hU]
        rw [← diagonal_add, diagonal_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
      have hdet : (1 + Q).det = ∏ i, (1 + (hQ.1.eigenvalues i : ℂ)) := by
        rw [hsum, det_mul, det_mul, det_diagonal, mul_comm, ← mul_assoc, ← det_mul, h2, det_one, one_mul]
      rw [hdet, show (∏ i, (1 + (hQ.1.eigenvalues i : ℂ))) = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) by
        push_cast; rfl, Complex.ofReal_re]
      calc (1 : ℝ) = ∏ _i : κ, (1 : ℝ) := by rw [Finset.prod_const_one]
        _ ≤ ∏ i, (1 + hQ.1.eigenvalues i) :=
          Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => le_add_of_nonneg_right (hQ.eigenvalues_nonneg i)
    intro κ _ _ X Y hX hP
    have hY : Y = X + (Y - X) := by abel
    by_cases h0 : X.det = 0
    · rw [h0, Complex.zero_re]
      have hnn := (hX.add hP).det_nonneg
      rw [← hY] at hnn
      exact (Complex.le_def.1 hnn).1
    · obtain ⟨U, h1, h2, hU⟩ := exists_unitary_diagonal_eigenvalues_of_isHermitian hX.1
      have hpos : ∀ i, 0 < hX.1.eigenvalues i := by
        intro i
        refine lt_of_le_of_ne (hX.eigenvalues_nonneg i) fun h => h0 ?_
        rw [hX.1.det_eq_prod_eigenvalues]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← h]; simp)
      set s : κ → ℂ := fun i => ((Real.sqrt (hX.1.eigenvalues i) : ℝ) : ℂ) with hs
      have hs0 : ∀ i, s i ≠ 0 := fun i => by
        simp only [hs, ne_eq, Complex.ofReal_eq_zero]
        exact (Real.sqrt_pos.2 (hpos i)).ne'
      have hss : ∀ i, s i * s i = (hX.1.eigenvalues i : ℂ) := fun i => by
        simp only [hs]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
      have hstar : ∀ i, star (s i) = s i := fun i => by simp [hs]
      set B : Matrix κ κ ℂ := diagonal s * star U with hB
      set C : Matrix κ κ ℂ := U * diagonal (fun i => (s i)⁻¹) with hC
      have hCB : C * B = 1 := by
        rw [hB, hC, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal,
          show (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) from funext fun i => inv_mul_cancel₀ (hs0 i),
          diagonal_one, Matrix.one_mul, h1]
      have hXB : X = Bᴴ * B := by
        rw [hB, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose,
          show star s = s from funext hstar, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s),
          diagonal_mul_diagonal, show (fun i => s i * s i) = fun i => (hX.1.eigenvalues i : ℂ) from funext hss,
          ← Matrix.mul_assoc, ← star_eq_conjTranspose]
        exact hU
      have hsplit : Y = Bᴴ * (1 + Cᴴ * (Y - X) * C) * B := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hXB, Matrix.mul_assoc, Matrix.mul_assoc, hCB,
          Matrix.mul_one, ← Matrix.mul_assoc, ← conjTranspose_mul, hCB, conjTranspose_one, Matrix.one_mul]
        abel
      have hQ : (Cᴴ * (Y - X) * C).PosSemidef := hP.conjTranspose_mul_mul_same C
      have hdX : X.det = Bᴴ.det * B.det := by rw [hXB, det_mul]
      clear_value B C
      have hdY : Y.det = (1 + Cᴴ * (Y - X) * C).det * X.det := by
        conv_lhs => rw [hsplit]
        rw [det_mul, det_mul, hdX]
        ring
      have hXnn := Complex.le_def.1 hX.det_nonneg
      have hQnn := Complex.le_def.1 (PosSemidef.one.add hQ).det_nonneg
      rw [hdY, Complex.mul_re, ← hXnn.2, ← hQnn.2]
      simp only [Complex.zero_im, mul_zero, sub_zero]
      have ha : 0 ≤ X.det.re := by simpa using hXnn.1
      exact le_mul_of_one_le_left ha (one_le_re_det_lemma_2 hQ))

end GlobalTheory.CompanionTheory.DetMonotone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfSumApplyEqZero
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.EvalTensor

variable {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]

theorem eq_zero_of_sum_apply_eq_zero (σ : Representation ℂ G S) (π : Representation ℂ G V)
    (hirr : σ.IsIrreducible)
    (hschur : ∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id)
    {ι : Type} (b : ι → (S →ₗ[ℂ] V)) (hli : LinearIndependent ℂ b)
    (hb : ∀ i g s, b i (σ g s) = π g (b i s)) (J : Finset ι) :
    ∀ t : ι → S, ∑ j ∈ J, b j (t j) = 0 → ∀ j ∈ J, t j = 0 := by
  classical
  haveI : IsSimpleOrder (Subrepresentation σ) := hirr
  induction J using Finset.induction_on with
  | empty => intro t _ j hj; simp at hj
  | insert a J ha ih =>
    intro t ht
    rw [Finset.sum_insert ha] at ht
    have hta : t a = 0 := by
      by_contra hne
      let Φ : (J → S) →ₗ[ℂ] V := ∑ j : J, (b j.1).comp (LinearMap.proj j)
      have hΦ : ∀ f : J → S, Φ f = ∑ j : J, b j.1 (f j) := fun f => by
        simp [Φ, LinearMap.sum_apply]
      have hinj : Function.Injective Φ := by
        rw [injective_iff_map_eq_zero]
        intro f hf
        rw [hΦ] at hf
        funext j
        have h0 := ih (fun i => if h : i ∈ J then f ⟨i, h⟩ else 0) (by
          rw [← Finset.sum_coe_sort J]
          simpa using hf) j.1 j.2
        simpa using h0
      have hequi : ∀ (g : G) (f : J → S), Φ (fun j => σ g (f j)) = π g (Φ f) := fun g f => by
        rw [hΦ, hΦ, map_sum]
        exact Finset.sum_congr rfl fun j _ => hb j.1 g (f j)
      let W : Subrepresentation σ :=
        { toSubmodule := (LinearMap.range Φ).comap (b a)
          apply_mem_toSubmodule := by
            rintro g v ⟨f, hf⟩
            exact ⟨fun j => σ g (f j), by rw [hequi, hf, hb]⟩ }
      have hmem : t a ∈ W := by
        refine ⟨fun j => - t j.1, ?_⟩
        rw [hΦ]
        have h1 : ∑ j : J, b j.1 (- t j.1) = - ∑ j ∈ J, b j (t j) := by
          rw [← Finset.sum_coe_sort J, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => map_neg _ _
        rw [h1]
        exact (eq_neg_of_add_eq_zero_left ht).symm ▸ rfl
      have htop : W = ⊤ := by
        rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
        · exfalso
          apply hne
          rw [h] at hmem
          exact hmem
        · exact h
      have hall : ∀ s, b a s ∈ LinearMap.range Φ := fun s => by
        have : s ∈ W := by rw [htop]; trivial
        exact this
      let e := LinearEquiv.ofInjective Φ hinj
      let B : S →ₗ[ℂ] (J → S) := e.symm.toLinearMap ∘ₗ (b a).codRestrict (LinearMap.range Φ) hall
      have hB : ∀ s, Φ (B s) = b a s := fun s => by
        have h1 : ((e (B s) : LinearMap.range Φ) : V) = Φ (B s) := LinearEquiv.ofInjective_apply _ _
        rw [← h1]
        simp [B]
      have hBc : ∀ g s, B (σ g s) = fun j => σ g (B s j) := fun g s => by
        apply hinj
        rw [hB, hequi, hB, hb]
      have hsc : ∀ j : J, ∃ c : ℂ, (LinearMap.proj j) ∘ₗ B = c • (LinearMap.id : S →ₗ[ℂ] S) := fun j =>
        hschur _ fun g s => by
          simp only [LinearMap.comp_apply, LinearMap.proj_apply]
          rw [hBc]
      choose c hc using hsc
      have hsum : b a = ∑ j : J, c j • b j.1 := by
        ext s
        rw [← hB, hΦ, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : B s j = c j • s := by
          simpa using LinearMap.congr_fun (hc j) s
        rw [h1, map_smul, LinearMap.smul_apply]
      refine hli.notMem_span_image (s := (J : Set ι)) (x := a) (by simpa using ha) ?_
      rw [hsum]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j.1, j.2, rfl⟩)
    have hrest : ∑ j ∈ J, b j (t j) = 0 := by
      simpa [hta] using ht
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hta
    · exact ih t hrest j hj

theorem lift_flip_subtype_injective : ∀ {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G S) (π : Representation ℂ G V), σ.IsIrreducible → (∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id) → ∀ M : Submodule ℂ (S →ₗ[ℂ] V), (∀ f ∈ M, ∀ g s, f (σ g s) = π g (f s)) → Function.Injective (TensorProduct.lift (LinearMap.flip (M.subtype)) : S ⊗[ℂ] M →ₗ[ℂ] V) := by
  intro G S V _ _ _ _ _ σ π hirr hschur M hM
  classical
  let β := Module.Basis.ofVectorSpace ℂ M
  have hli : LinearIndependent ℂ (fun i => ((β i : M) : S →ₗ[ℂ] V)) :=
    β.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  rw [injective_iff_map_eq_zero]
  intro x hx
  let E := TensorProduct.equivFinsuppOfBasisRight (M := S) β
  have hxs : x = (E x).sum fun i s => s ⊗ₜ[ℂ] β i := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hsum : ∑ i ∈ (E x).support, ((β i : M) : S →ₗ[ℂ] V) (E x i) = 0 := by
    rw [hxs, Finsupp.sum, map_sum] at hx
    simpa using hx
  have h0 := eq_zero_of_sum_apply_eq_zero σ π hirr hschur _ hli
    (fun i g s => hM _ (β i).2 g s) (E x).support (fun i => E x i) hsum
  have hE : E x = 0 := by
    ext i
    by_cases hi : i ∈ (E x).support
    · simpa using h0 i hi
    · simpa using hi
  exact E.map_eq_zero_iff.1 hE

end GlobalTheory.CompanionTheory.EvalTensor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleSurjectiveLocalSection
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.EtaleSections

theorem exists_algHom_away_of_etale {S : Type} [CommRing S] (hA : Aic S) (hL : Loc S)
    (B : Type) [CommRing B] [Algebra S B] [Algebra.Etale S B] (Q : Ideal B) [hQ : Q.IsPrime]
    (hm : (Q.comap (algebraMap S B)).IsMaximal) :
    ∃ e : S, IsIdempotentElem e ∧ e ∉ Q.comap (algebraMap S B) ∧
      Nonempty (B →ₐ[S] Localization.Away e) := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := S) Q
  let Bg := Localization.Away g
  have hdisj : Disjoint (Submonoid.powers g : Set B) (Q : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (hQ.mem_of_pow_mem n hn)
  have hQ' : (Q.map (algebraMap B Bg)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Bg Q hQ hdisj
  have hcomap : (Q.map (algebraMap B Bg)).comap (algebraMap B Bg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Bg hQ hdisj
  have hc : (Q.map (algebraMap B Bg)).comap (algebraMap S Bg) = Q.comap (algebraMap S B) := by
    rw [IsScalarTower.algebraMap_eq S B Bg, ← Ideal.comap_comap, hcomap]
  obtain ⟨e, he, hem, ⟨ψ⟩⟩ := GlobalTheory.CompanionTheory.EtaleSection.exists_section_standardEtale hA hL Bg (Q.map (algebraMap B Bg)) hQ' (hc ▸ hm)
  exact ⟨e, he, hc ▸ hem, ⟨ψ.comp (IsScalarTower.toAlgHom S B Bg)⟩⟩

theorem exists_secOn_of_etale_surjective : ∀ {S : Type} [CommRing S] , Aic S → Loc S →
    ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f →
    ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  intro S _ hA hL Y f hE hS m hm
  let x : Spec (CommRingCat.of S) := ⟨m, hm.isPrime⟩
  obtain ⟨y, hy⟩ := hS.surj x
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ f)
  have hEt : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt
  let _ : Algebra S Γ(Y, V) := φ.hom.toAlgebra
  have : Algebra.Etale S Γ(Y, V) := RingHom.etale_algebraMap.1 hφe
  have hyr : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
  obtain ⟨z, hz⟩ := hyr
  have hcm : z.asIdeal.comap (algebraMap S Γ(Y, V)) = m := by
    have h1 : (Spec.map φ) z = x := by
      rw [hφ, Scheme.Hom.comp_apply, hz, hy]
    exact congrArg PrimeSpectrum.asIdeal h1
  have : z.asIdeal.IsPrime := z.2
  obtain ⟨e, he, hem, ⟨ψ⟩⟩ := exists_algHom_away_of_etale hA hL Γ(Y, V) z.asIdeal (by rw [hcm]; exact hm)
  refine ⟨e, he, hcm ▸ hem, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  congr 1
  ext a
  exact ψ.commutes a

end GlobalTheory.CompanionTheory.EtaleSections
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLattice
section
open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi

noncomputable section
namespace GlobalTheory.CompanionTheory.CharacterBiduality

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indicator_mem_SB {n : ℕ} (A : AddSubgroup (Fin n → k))
    (hAc : IsCompact (A : Set (Fin n → k))) (hAo : IsOpen (A : Set (Fin n → k))) :
    (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (Fin n → k) := by
  have hcl : IsClopen (A : Set (Fin n → k)) := ⟨AddSubgroup.isClosed_of_isOpen A hAo, hAo⟩
  exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩

theorem fourier_sub_translate_eq_zero [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ : AddChar k Circle) (hψ : Continuous ψ) (μ : Measure (Fin n → k)) [μ.IsAddHaarMeasure]
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k)))
    (hAo : IsOpen (A : Set (Fin n → k))) (x : Fin n → k)
    (hx : ∀ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) → ψ (η ⬝ᵥ x) = 1) (y : Fin n → k) :
    ∫ z, ((A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) z -
        (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hc : Continuous fun z : Fin n → k => (ψ (z ⬝ᵥ y) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (continuous_id.dotProduct continuous_const))
  have hi1 : Integrable (fun z => g z * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    (hg.1.continuous.mul hc).integrable_of_hasCompactSupport hg.2.mul_right
  have hgx : HasCompactSupport fun z => g (z + x) := hg.2.comp_homeomorph (Homeomorph.addRight x)
  have hi2 : Integrable (fun z => g (z + x) * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    ((hg.1.continuous.comp (continuous_id.add continuous_const)).mul hc).integrable_of_hasCompactSupport
      hgx.mul_right
  have e1 : ∫ z, g (z + x) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ =
      (ψ (-(x ⬝ᵥ y)) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
    have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ ((w - x) ⬝ᵥ y) : ℂ)) x
    simp only [add_sub_cancel_right] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hwx : (w - x) ⬝ᵥ y = w ⬝ᵥ y + -(x ⬝ᵥ y) := by rw [sub_dotProduct, sub_eq_add_neg]
    beta_reduce
    rw [hwx, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [sub_mul]
  rw [integral_sub hi1 hi2, e1]
  by_cases hy : ∀ a ∈ A, ψ (y ⬝ᵥ a) = 1
  · have h1 : ψ (x ⬝ᵥ y) = 1 := by rw [dotProduct_comm]; exact hx y hy
    have h2 : ψ (-(x ⬝ᵥ y)) = 1 := by rw [AddChar.map_neg_eq_inv, h1, inv_one]
    simp [h2]
  · push Not at hy
    obtain ⟨a, haA, hne⟩ := hy
    have h0 : ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
      have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ (w ⬝ᵥ y) : ℂ)) a
      have h3 : ∫ z, g (z + a) * (ψ ((z + a) ⬝ᵥ y) : ℂ) ∂μ =
          (ψ (y ⬝ᵥ a) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        have hga : g (w + a) = g w := by
          by_cases hw : w ∈ A
          · simp [hgdef, Set.indicator, hw, A.add_mem hw haA]
          · have : w + a ∉ A := fun h => hw (by simpa using A.sub_mem h haA)
            simp [hgdef, Set.indicator, hw, this]
        simp only [hga, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm a y]
        ring
      rw [h3] at h
      have h4 : (1 - (ψ (y ⬝ᵥ a) : ℂ)) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
        rw [sub_mul, one_mul, h, sub_self]
      refine (mul_eq_zero.1 h4).resolve_left fun h5 => hne (Circle.ext ?_)
      simpa using (sub_eq_zero.1 h5).symm
    simp [h0]

theorem exists_annihilator_ne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A →
    ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo x hxA
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := secondCountable k
  haveI := t2Space k
  let μ : Measure (Fin n → k) := Measure.addHaar
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hgx : (fun z => g (z + x)) ∈ SB (Fin n → k) :=
    ⟨hg.1.comp_continuous (continuous_id.add continuous_const),
      hg.2.comp_homeomorph (Homeomorph.addRight x)⟩
  have hf : (fun z => g z - g (z + x)) ∈ SB (Fin n → k) := (SB (Fin n → k)).sub_mem hg hgx
  obtain ⟨s, hs⟩ := fourier_inversion_pi μ hc hf
  have hz : ∀ y : Fin n → k, ∫ z, (g z - g (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 :=
    fourier_sub_translate_eq_zero ψ hψ μ A hAc hAo x hcon
  simp only [hz, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (box (Fin n) r) := fun r => by
    have h1 : (0 : Fin n → k) ∈ box (Fin n) r := fun i _ => by simp [cball]
    have h2 : 0 < μ (box (Fin n) r) := (isOpen_box r).measure_pos μ ⟨0, h1⟩
    exact ENNReal.toReal_pos h2.ne' (isCompact_box r).measure_lt_top.ne
  have hne : ((μ.real (box (Fin n) s) * μ.real (box (Fin n) (c * s⁻¹)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (hpos s) (hpos _)).ne'
  have h0 : g 0 - g (0 + x) = 0 := (mul_eq_zero.mp hs.symm).resolve_left hne
  have hg0 : g 0 = 1 := Set.indicator_of_mem (SetLike.mem_coe.2 A.zero_mem) _
  have hgx0 : g (0 + x) = 0 := by
    rw [zero_add]
    exact Set.indicator_of_notMem (fun h => hxA h) _
  rw [hg0, hgx0] at h0
  simp at h0

end GlobalTheory.CompanionTheory.CharacterBiduality
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNcardEntrywiseBoxLe
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Counting

open GroundTheory.Automorphic.CuspidalSpectrum in

theorem exists_ncard_entrywiseBox_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    (𝒦 : Set (FiniteAdeleRing (𝓞 K) K)) (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ T i j) →
      (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)).Finite ∧
      ((Set.ncard (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)) : ℕ) : ℝ) ≤
        ∏ i, ∏ j, C * (1 + T i j) ^ Module.finrank ℚ K := by
  obtain ⟨m, hm, hint⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact K h𝒦
  obtain ⟨C₀, hC₀, hcount⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_integers_le K
  have hw : ∀ (w : InfinitePlace K) (x : K), w ((m : K) * x) = (m : ℝ) * w x := by
    intro w x
    rw [← w.norm_embedding_eq, map_mul, norm_mul, w.norm_embedding_eq, w.norm_embedding_eq, w.map_natCast]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨C₀ * (m : ℝ) ^ Module.finrank ℚ K, mul_nonneg hC₀ (by positivity), ?_⟩
  intro T hT
  have hA : ∀ p : Fin n × Fin n,
      (((↑) : 𝓞 K → K) '' {z | ∀ w : InfinitePlace K, w (z : K) ≤ (m : ℝ) * T p.1 p.2}).Finite ∧
      ((((↑) : 𝓞 K → K) '' {z | ∀ w : InfinitePlace K, w (z : K) ≤ (m : ℝ) * T p.1 p.2}).ncard : ℝ) ≤
        C₀ * (1 + (m : ℝ) * T p.1 p.2) ^ Module.finrank ℚ K := by
    intro p
    obtain ⟨hf, hc⟩ := hcount ((m : ℝ) * T p.1 p.2) (mul_nonneg (by positivity) (hT p.1 p.2))
    exact ⟨hf.image _, le_trans (by exact_mod_cast Set.ncard_image_le hf) hc⟩
  let F : GL (Fin n) K → (Fin n × Fin n → K) := fun γ p => (m : K) * (γ : Matrix (Fin n) (Fin n) K) p.1 p.2
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin n × Fin n → K), t = Fintype.piFinset fun p => (hA p).1.toFinset := ⟨_, rfl⟩
  have key : ∀ γ : GL (Fin n) K, (∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
      ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j) → F γ ∈ (t : Set (Fin n × Fin n → K)) := by
    intro γ hγ
    rw [Finset.mem_coe, ht, Fintype.mem_piFinset]
    intro p
    rw [Set.Finite.mem_toFinset]
    obtain ⟨z, hz⟩ := hint _ (hγ p.1 p.2).1
    refine ⟨z, fun w => ?_, hz⟩
    rw [hz, hw]
    exact mul_le_mul_of_nonneg_left ((hγ p.1 p.2).2 w) (by positivity)
  have inj : ∀ γ γ' : GL (Fin n) K, F γ = F γ' → γ = γ' := by
    intro γ γ' h
    ext i j
    exact mul_left_cancel₀ hmK (congrFun h (i, j))
  refine ⟨?_, ?_⟩
  · exact Set.Finite.of_finite_image ((t.finite_toSet).subset (Set.image_subset_iff.mpr fun γ hγ => key γ hγ))
      (fun γ _ γ' _ h => inj γ γ' h)
  · refine le_trans (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn F (fun γ hγ => key γ hγ)
      (fun γ _ γ' _ h => inj γ γ' h) t.finite_toSet)) ?_
    rw [Set.ncard_coe_finset, ht, Fintype.card_piFinset, Nat.cast_prod, Fintype.prod_prod_type]
    apply Finset.prod_le_prod (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
    intro i _
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro j _
    rw [← Set.ncard_eq_toFinset_card _ (hA (i, j)).1]
    refine le_trans (hA (i, j)).2 ?_
    rw [mul_assoc, ← mul_pow]
    apply mul_le_mul_of_nonneg_left _ hC₀
    apply pow_le_pow_left₀ (by nlinarith [hT i j])
    nlinarith [hT i j]

end GlobalTheory.CompanionTheory.Counting
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirst
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLen

theorem isFiniteLength_of_ker_le_range {W : Type} [CommRing W] {A B C : Type 1}
    [AddCommGroup A] [Module W A] [AddCommGroup B] [Module W B] [AddCommGroup C] [Module W C]
    (v : A →ₗ[W] B) (f : B →ₗ[W] C) (h : LinearMap.ker f ≤ LinearMap.range v)
    (hA : IsFiniteLength W A) (hC : IsFiniteLength W C) : IsFiniteLength W B := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hA hC ⊢
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hC
  have n1 : IsNoetherian W (LinearMap.range v) :=
    isNoetherian_of_surjective v.rangeRestrict (LinearMap.range_rangeRestrict v)
  have a1 : IsArtinian W (LinearMap.range v) :=
    isArtinian_of_surjective A v.rangeRestrict v.surjective_rangeRestrict
  have n2 : IsNoetherian W (LinearMap.ker f) :=
    isNoetherian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have a2 : IsArtinian W (LinearMap.ker f) :=
    isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have hr : LinearMap.range (LinearMap.ker f).subtype = LinearMap.ker f.rangeRestrict := by
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  exact ⟨isNoetherian_of_range_eq_ker _ _ hr, isArtinian_of_range_eq_ker _ _ hr⟩

theorem isFiniteLength_level : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  intro W _ l S S' L h1 n
  induction n with
  | zero =>
    have : Subsingleton (S.M 0) := ⟨fun x y => by
      have hx := L.kill 0 x
      have hy := L.kill 0 y
      simp only [pow_zero, one_smul] at hx hy
      rw [hx, hy]⟩
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    refine isFiniteLength_of_ker_le_range (L.ν 1 (n + 1)) (L.ρ (n + 1) n) ?_ h1 ih
    intro x hx
    obtain ⟨y, hy⟩ := L.ex₁ 1 n (n + 1) (by omega) x hx
    exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.TowerLen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUniqueStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_exists_unique : PositivityTheory.Lbc.HeckeExistsUnique := by
  first | exact @GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | exact GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | (intros; apply GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique <;> assumption)
end

