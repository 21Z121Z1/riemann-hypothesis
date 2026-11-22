import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignature
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.EigenvalueNormSignature

theorem form_mulVec {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star (M *ᵥ x) ⬝ᵥ A *ᵥ (M *ᵥ y) = star x ⬝ᵥ (Mᴴ * A * M) *ᵥ y := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem det_ne_zero_of_sig {n : ℕ} {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian)
    (hs : sigPosH hh + sigNegH hh = n) : h.det ≠ 0 := by
  intro hd
  rw [hh.det_eq_prod_eigenvalues] at hd
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hd
  have hi0 : hh.eigenvalues i = 0 := by simpa using hi
  unfold sigPosH sigNegH at hs
  have hdis : Disjoint (fun j : Fin n => 0 < hh.eigenvalues j) (fun j => hh.eigenvalues j < 0) := by
    rw [Pi.disjoint_iff]; intro j
    simp only [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩; linarith
  rw [← Fintype.card_subtype_or_disjoint _ _ hdis] at hs
  have hlt : Fintype.card {j : Fin n // 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0} < Fintype.card (Fin n) :=
    Fintype.card_subtype_lt (p := fun j => 0 < hh.eigenvalues j ∨ hh.eigenvalues j < 0) (x := i)
      (by rw [hi0]; simp)
  rw [Fintype.card_fin] at hlt
  omega

end GlobalTheory.EigenvalueNormSignature

namespace GlobalTheory

open GlobalTheory.EigenvalueNormSignature in

theorem eig_norm_sq_of_similitude : ∀ (n : ℕ) (h Q Γ : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (c : ℝ),
    sigPosH hh ≤ 1 → sigPosH hh + sigNegH hh = n → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * Z → c ≠ 0 →
    Γᴴ * Q * Γ = (c : ℂ) • Q →
    (sigPosH hh = 0 ∨ ∃ (μ : ℂ) (x₀ : Fin n → ℂ), Γ *ᵥ x₀ = μ • x₀ ∧ 0 < (star x₀ ⬝ᵥ (Q *ᵥ x₀)).re) →
    ∀ (w : ℂ) (x : Fin n → ℂ), x ≠ 0 → Γ *ᵥ x = w • x → ‖w‖ ^ 2 = c := by
  intro n h Q Γ hh Z c hle hs hQ hc hΓ hcase w x hx hw
  have hdet := det_ne_zero_of_sig hh hs
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hZinj : ∀ v : Fin n → ℂ, v ≠ 0 → Zm *ᵥ v ≠ 0 := by
    intro v hv h0
    apply hv
    have : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ (Zm *ᵥ v) = v := by
      rw [mulVec_mulVec, hZm, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hB : ∀ u v : Fin n → ℂ, star u ⬝ᵥ Q *ᵥ v = star (Zm *ᵥ u) ⬝ᵥ h *ᵥ (Zm *ᵥ v) := by
    intro u v; rw [form_mulVec, hQ]

  have hsim : ∀ (a b : ℂ) (u v : Fin n → ℂ), Γ *ᵥ u = a • u → Γ *ᵥ v = b • v →
      (star a * b - c) * (star u ⬝ᵥ Q *ᵥ v) = 0 := by
    intro a b u v hu hv
    have e := form_mulVec Γ Q u v
    rw [hΓ, hu, hv] at e
    simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_mulVec] at e
    rw [RCLike.star_def] at e ⊢
    linear_combination e
  have hnorm : ∀ a : ℂ, star a * a = (c : ℂ) → ‖a‖ ^ 2 = c := by
    intro a ha
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = c := by
      rw [← ha, RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast this
  by_cases hq : star x ⬝ᵥ Q *ᵥ x = 0
  · rcases hcase with h0 | ⟨μ, x₀, hμ, hpos⟩
    · have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x) (hZinj x hx)
      rw [← hB, hq] at this; simp at this
    · have h1 : sigPosH hh = 1 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
        · have hx₀ : x₀ ≠ 0 := by rintro rfl; simp at hpos
          have := herm_negDef_of_sigPosH_eq_zero h hh hdet h0 (Zm *ᵥ x₀) (hZinj x₀ hx₀)
          rw [← hB] at this; linarith
        · exact h1
      have hμμ := hsim μ μ x₀ x₀ hμ hμ
      have hq0 : star x₀ ⬝ᵥ Q *ᵥ x₀ ≠ 0 := fun e => by rw [e] at hpos; simp at hpos
      have hμc : star μ * μ = (c : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hμμ).resolve_right hq0)
      by_cases hb : star x₀ ⬝ᵥ Q *ᵥ x = 0
      · have := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet h1 (Zm *ᵥ x₀) (Zm *ᵥ x)
          (by rw [← hB]; exact hpos) (by rw [← hB]; exact hb) (hZinj x hx)
        rw [← hB, hq] at this; simp at this
      · have hμw := sub_eq_zero.mp ((mul_eq_zero.mp (hsim μ w x₀ x hμ hw)).resolve_right hb)
        have hμ0 : star μ ≠ 0 := by
          intro e; rw [e, zero_mul] at hμc; exact hc (by exact_mod_cast hμc.symm)
        have hwμ : w = μ := mul_left_cancel₀ hμ0 (hμw.trans hμc.symm)
        rw [hwμ]; exact hnorm μ hμc
  · exact hnorm w (sub_eq_zero.mp ((mul_eq_zero.mp (hsim w w x x hw hw)).resolve_right hq))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConjOnFinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjCharUnique

theorem eq_of_conj_on_finite {D : D7} {σ : D.what₂.LL →+* ℂ} {μ μ' μ'' : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D μ') (g1 : IsHeckeChar D μ'')
    (h : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ' x : Circle) : ℂ) = σ y)
    (g : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : D.what₂.LL,
      ((μ x : Circle) : ℂ) = D.what₂.embLL y ∧ ((μ'' x : Circle) : ℂ) = σ y) : μ' = μ'' := by
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (μ' * μ''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h y hy
  obtain ⟨b, hb, hb'⟩ := g y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.symm.trans hb)
  exact Subtype.ext (ha'.trans hb'.symm)

theorem conjChar_unique : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), (∀ μ' μ'', ChiAt R i σ μ' → ChiAt R i σ μ'' → μ' = μ'') ∧ ∀ η' η'', IsEtaConj σ R.eta η' → IsEtaConj σ R.eta η'' → η' = η'' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i σ
  refine ⟨fun μ' μ'' h g => eq_of_conj_on_finite (σ := σ) (μ := R.mu0 ((i : ℕ) + 1)) h.1 g.1
    (fun x hx => (h.2.2.2.1 x hx).elim fun y hy => ⟨_, hy⟩) (fun x hx => (g.2.2.2.1 x hx).elim fun y hy => ⟨_, hy⟩),
    fun η' η'' h g => GlobalTheory.UnramCharUnique.isEtaConj_unique D σ R.eta η' η'' h g⟩

end GlobalTheory.ConjCharUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwinStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K)) (Φ : ContinuousMultilinearMap ℂ M.H K), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) → ∀ v : M.Vec, IsSmoothVector' θ V ρ (Φ fun τ => (v τ : M.H τ)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) = Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))) := by
  first | exact @GlobalTheory.SmoothMultilinear.smooth_map | exact GlobalTheory.SmoothMultilinear.smooth_map | (intros; apply GlobalTheory.SmoothMultilinear.smooth_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalAffineIndEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
theorem _root_.GlobalTheory.T.etaleCohomology_local_to_global_affine_indEtale : ∀ (q : ℕ) (B : Type) [CommRing B] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of B)) [QuasiCompact f] [QuasiSeparated f], IsUnit (q : B) → ∀ i : ℤ, (∀ (A : Type) [CommRing A] [Algebra B A], SH A → IndEt B A → Eqv _ (sch.map (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B A))))) (tw q i)) → Eqv _ (sch.map f) (tw q i) := by
  first | exact @GlobalTheory.LocGlobIndEt.main | exact GlobalTheory.LocGlobIndEt.main | (intros; apply GlobalTheory.LocGlobIndEt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C), (∀ (O : Type) [CommRing O] [Algebra A O], SH O → IndEt A O → Eqv R (spMap (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) F) → Eqv R (spMap φ.toRingHom) F := by
  first | (exact @GlobalTheory.LocGlobRing.main) | (exact GlobalTheory.LocGlobRing.main) | (intros; apply GlobalTheory.LocGlobRing.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesStalkFlat
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}}
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U →
    _root_.GlobalTheory.LogPair.IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U),
    ((Y.presheaf.germ U y hy).hom.comp (_root_.GlobalTheory.LogPair.cstOn g U)).Flat := by
  intro R _ Y g U n t hU ht y hy
  have hC : (MvPolynomial.C : R →+* MvPolynomial (Fin n) R).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have hE : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Flat := by
    have h : (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).Etale := ht
    letI := (MvPolynomial.eval₂Hom (_root_.GlobalTheory.LogPair.cstOn g U) t).toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(Y, U) := h
    show Module.Flat _ _
    infer_instance
  have hG : (Y.presheaf.germ U y hy).hom.Flat := by
    letI := (Y.presheaf.germ U y hy).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨y, hy⟩
    show Module.Flat _ _
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  rw [← MvPolynomial.eval₂Hom_comp_C (_root_.GlobalTheory.LogPair.cstOn g U) t, ← RingHom.comp_assoc]
  exact (hC.comp hE).comp hG

end GlobalTheory.LogPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.ClosedCover

theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id]
  exact sch.map_id _

theorem pull_spMap_bij {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (n i : ℤ) :
    Function.Bijective (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n) := by
  have h1 : ∀ x, pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp]
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext; simp
    rw [this, spMap_id, pull_id]
  have h2 : ∀ x, pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem polyProd_bij (A B : Type) [CommRing A] [CommRing B] :
    Function.Bijective ((Polynomial.mapRingHom (RingHom.fst A B)).prod (Polynomial.mapRingHom (RingHom.snd A B))) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    simp only [RingHom.prod_apply, Prod.mk_eq_zero, Polynomial.coe_mapRingHom] at hp
    ext n
    · simpa using congrArg (fun r => Polynomial.coeff r n) hp.1
    · simpa using congrArg (fun r => Polynomial.coeff r n) hp.2
  · rintro ⟨p, p'⟩
    let N := max p.natDegree p'.natDegree + 1
    refine ⟨∑ k ∈ Finset.range N, Polynomial.monomial k (p.coeff k, p'.coeff k), ?_⟩
    simp only [RingHom.prod_apply, Polynomial.coe_mapRingHom, Polynomial.map_sum, Polynomial.map_monomial]
    refine Prod.ext ?_ ?_
    · exact (Polynomial.as_sum_range' p N (by omega)).symm
    · exact (Polynomial.as_sum_range' p' N (by omega)).symm

theorem prodL : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], HInv q A → HInv q B → HInv q (A × B) := by
  intro q _ A B _ _ hA hB i n
  let e : Polynomial (A × B) ≃+* Polynomial A × Polynomial B := RingEquiv.ofBijective _ (polyProd_bij A B)
  let g : A × B →+* Polynomial A × Polynomial B := RingHom.prodMap Polynomial.C Polynomial.C
  have hg : e.toRingHom.comp Polynomial.C = g := by
    ext x <;> simp [e, g]

  have hgb : Function.Bijective (pull (ZMod q) (spMap g) (tw q i) n) := by
    have hP := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B n i
    have hD := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (Polynomial A) (Polynomial B) n i
    have hsq : ∀ x : Ht q (sp (A × B)) n i,
        (pull _ (spMap (RingHom.fst (Polynomial A) (Polynomial B))) _ _ (pull _ (spMap g) _ n x),
          pull _ (spMap (RingHom.snd (Polynomial A) (Polynomial B))) _ _ (pull _ (spMap g) _ n x)) =
        Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n)
          (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x) := by
      intro x
      simp only [Prod.map]
      rw [← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, ← spMap_comp, ← spMap_comp]
      rfl
    have hcomp : (fun x : Ht q (sp (Polynomial A × Polynomial B)) n i =>
          (pull _ (spMap (RingHom.fst (Polynomial A) (Polynomial B))) _ _ x,
           pull _ (spMap (RingHom.snd (Polynomial A) (Polynomial B))) _ _ x)) ∘ (pull _ (spMap g) _ n) =
        Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
          (fun x : Ht q (sp (A × B)) n i =>
            (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
      funext x; exact hsq x
    have hR : Function.Bijective (Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n)) :=
      Function.Bijective.prodMap (hA i n) (hB i n)
    have := (hR.comp hP)
    rw [← hcomp] at this
    exact (Function.Bijective.of_comp_iff' hD _).mp this
  have heq : ⇑(pull (ZMod q) (spMap g) (tw q i) n) =
      ⇑(pull (ZMod q) (spMap e.toRingHom) (tw q i) n) ∘ ⇑(pull (ZMod q) (spMap (Polynomial.C : A × B →+* Polynomial (A × B))) (tw q i) n) := by
    funext x
    rw [Function.comp_apply, ← pull_comp, ← spMap_comp, hg]
  rw [heq] at hgb
  exact (Function.Bijective.of_comp_iff' (pull_spMap_bij e n i) _).mp hgb

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover
open PiTensorProduct

noncomputable def consLin (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) :
    B ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => B) ≃ₗ[A] PiTensorProduct A (fun _ : Fin (k + 2) => B) :=
  (TensorProduct.congr (subsingletonEquiv (R := A) (s := fun _ : Fin 1 => B) (0 : Fin 1)).symm (LinearEquiv.refl A _)).trans <|
    (tmulEquiv A B).trans (reindex A (fun _ => B) (finSumFinEquiv.trans (finCongr (by omega))))

theorem consLin_tmul (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (b : B) (x : Fin (k + 1) → B) :
    consLin A B k (b ⊗ₜ PiTensorProduct.tprod A x) =
      PiTensorProduct.tprod A (fun i => Sum.elim (fun _ : Fin 1 => b) x ((finSumFinEquiv.trans (finCongr (by omega))).symm i)) := by
  simp [consLin, reindex_tprod]

theorem succL : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ), Nonempty (PiTensorProduct A (fun _ : Fin (k + 2) => B) ≃ₐ[A] B ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => B)) := by
  intro A B _ _ _ k
  refine ⟨(AlgEquiv.ofLinearEquiv (consLin A B k) ?_ ?_).symm⟩
  · rw [Algebra.TensorProduct.one_def, PiTensorProduct.one_def, consLin_tmul, PiTensorProduct.one_def]
    congr 1
    funext i
    rcases (finSumFinEquiv.trans (finCongr (by omega))).symm i with j | j <;> rfl
  · refine (LinearMap.map_mul_iff _).mpr ?_
    ext b x b' x'
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod, consLin_tmul, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.compMultilinearMap_apply, LinearMap.restrictScalars_apply]
    congr 1
    funext i
    simp only [Pi.mul_apply]
    rcases (finSumFinEquiv.trans (finCongr (by omega))).symm i with j | j <;> rfl
end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

theorem oneL : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (PiTensorProduct A (fun _ : Fin 1 => B) ≃ₐ[A] B) := by
  intro A B _ _ _
  classical
  let f := PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin 1 => B) 0
  let g := PiTensorProduct.subsingletonEquiv (R := A) (s := fun _ : Fin 1 => B) (0 : Fin 1)
  have hgf : ∀ a, g (f a) = a := by
    intro a
    simp [f, g, PiTensorProduct.subsingletonEquiv_apply_tprod]
  have hf : Function.Bijective f := by
    have : (f : B → _) = g.symm := by
      funext a
      apply g.injective
      rw [hgf, LinearEquiv.apply_symm_apply]
    rw [this]
    exact g.symm.bijective
  exact ⟨(AlgEquiv.ofBijective f hf).symm⟩
end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

variable {A : Type} [CommRing A]

noncomputable def quotTensorQuot (L K : Ideal A) : (A ⧸ L) ⊗[A] (A ⧸ K) ≃ₐ[A] A ⧸ (L ⊔ K) :=
  ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ L) K).restrictScalars A).symm.trans
    (DoubleQuot.quotQuotEquivQuotSupₐ A L K)

noncomputable def prodLeftAlg (X Y C : Type) [CommRing X] [CommRing Y] [CommRing C] [Algebra A X] [Algebra A Y]
    [Algebra A C] : (X × Y) ⊗[A] C ≃ₐ[A] (X ⊗[A] C) × (Y ⊗[A] C) :=
  (Algebra.TensorProduct.comm A (X × Y) C).trans <|
    (Algebra.TensorProduct.prodRight A A C X Y).trans <|
      AlgEquiv.prodCongr (Algebra.TensorProduct.comm A C X) (Algebra.TensorProduct.comm A C Y)

noncomputable def stepEquiv (L I J : Ideal A) (C : Type) [CommRing C] [Algebra A C] :
    (A ⧸ L) ⊗[A] (((A ⧸ I) × (A ⧸ J)) ⊗[A] C) ≃ₐ[A] ((A ⧸ (L ⊔ I)) ⊗[A] C) × ((A ⧸ (L ⊔ J)) ⊗[A] C) :=
  (Algebra.TensorProduct.assoc A A A (A ⧸ L) ((A ⧸ I) × (A ⧸ J)) C).symm.trans <|
    (Algebra.TensorProduct.congr ((Algebra.TensorProduct.prodRight A A (A ⧸ L) (A ⧸ I) (A ⧸ J)).trans
      (AlgEquiv.prodCongr (quotTensorQuot L I) (quotTensorQuot L J))) AlgEquiv.refl).trans <|
    prodLeftAlg _ _ C

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

variable {A : Type} [CommRing A]

theorem hinv_of_algEquiv {q : ℕ} [NeZero q] {X Y : Type} [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (e : X ≃ₐ[A] Y) (h : HInv q X) : HInv q Y :=
  GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q X Y e.toRingEquiv h

def Good (I J L : Ideal A) : Prop := L = I ∨ L = J ∨ L = I ⊔ J

theorem good_sup_left {I J L : Ideal A} (h : Good I J L) : Good I J (L ⊔ I) := by
  rcases h with rfl | rfl | rfl
  · left; simp
  · right; right; exact sup_comm _ _
  · right; right; rw [sup_assoc, sup_comm J I, ← sup_assoc, sup_idem]

theorem good_sup_right {I J L : Ideal A} (h : Good I J L) : Good I J (L ⊔ J) := by
  rcases h with rfl | rfl | rfl
  · right; right; rfl
  · right; left; simp
  · right; right; rw [sup_assoc, sup_idem]

theorem main_step (q : ℕ) [NeZero q] (I J : Ideal A) (C : Type) [CommRing C] [Algebra A C]
    (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] (((A ⧸ I) × (A ⧸ J)) ⊗[A] C)) := by
  intro L hL
  exact hinv_of_algEquiv (stepEquiv L I J C).symm
    (prodL q _ _ (hC _ (good_sup_left hL)) (hC _ (good_sup_right hL)))

theorem main_fin (q : ℕ) [NeZero q] (I J : Ideal A) (C : Type) [CommRing C] [Algebra A C]
    (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    HInv q (((A ⧸ I) × (A ⧸ J)) ⊗[A] C) :=
  hinv_of_algEquiv (prodLeftAlg _ _ C).symm (prodL q _ _ (hC I (Or.inl rfl)) (hC J (Or.inr (Or.inl rfl))))

theorem good_congr (q : ℕ) [NeZero q] (I J : Ideal A) {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (e : C ≃ₐ[A] D) (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] D) := fun L hL =>
  hinv_of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : (A ⧸ L) ≃ₐ[A] (A ⧸ L)) e) (hC L hL)

theorem tensorPow (q : ℕ) [NeZero q] (I J : Ideal A)
    (hI : HInv q (A ⧸ I)) (hJ : HInv q (A ⧸ J)) (hIJ : HInv q (A ⧸ (I ⊔ J))) (k : ℕ) :
    (∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => (A ⧸ I) × (A ⧸ J)))) ∧
    HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => (A ⧸ I) × (A ⧸ J))) := by
  have h0 : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] A) := by
    intro L hL
    refine hinv_of_algEquiv (Algebra.TensorProduct.rid A A (A ⧸ L)).symm ?_
    rcases hL with rfl | rfl | rfl
    exacts [hI, hJ, hIJ]
  induction k with
  | zero =>
    obtain ⟨e⟩ := oneL A ((A ⧸ I) × (A ⧸ J))
    let e' := e.trans (Algebra.TensorProduct.rid A A ((A ⧸ I) × (A ⧸ J))).symm
    exact ⟨good_congr q I J e'.symm (main_step q I J A h0),
      hinv_of_algEquiv e'.symm (main_fin q I J A h0)⟩
  | succ k ih =>
    obtain ⟨e⟩ := succL A ((A ⧸ I) × (A ⧸ J)) k
    exact ⟨good_congr q I J e.symm (main_step q I J _ ih.1),
      hinv_of_algEquiv e.symm (main_fin q I J _ ih.1)⟩

theorem closedCover : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I J : Ideal A), I ⊓ J ≤ nilradical A →
    IsUnit (q : A) → HInv q (A ⧸ I) → HInv q (A ⧸ J) → HInv q (A ⧸ (I ⊔ J)) → HInv q A := by
  intro q _ A _ I J hn hq hI hJ hIJ
  refine GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q A ((A ⧸ I) × (A ⧸ J)) inferInstance ?_ hq (fun k => (tensorPow q I J hI hJ hIJ k).2)
  intro x hx
  apply hn
  rw [RingHom.mem_ker] at hx
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp h1, Ideal.Quotient.eq_zero_iff_mem.mp h2⟩

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

end GlobalTheory.EtC.ClosedCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIsIntegralInCompletedTensorBasisMulExp
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_mul (G : HTGroup p) (v : AwayP p) (a b : Qv v ⊗[ℚ] G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (a * b) k = ∑ i, ∑ j, (basV G v).repr a i * (basV G v).repr b j *
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) := by
  conv_lhs => rw [← (basV G v).sum_repr a, ← (basV G v).sum_repr b]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul, basV, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.mapRange_apply]
  rw [Finset.sum_comm]

omit [Fact p.Prime] in

theorem eventually_rat_mem_integers (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  exact Subtype.val_injective.tendsto_cofinite.eventually h

theorem isIntV_mul_eventually (G : HTGroup p) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  have h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem_integers _
  filter_upwards [h] with v hv a b ha hb k
  rw [basV_repr_mul]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (ha i) (hb j)) (hv i j k)

theorem isIntV_mul_eventually' : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) :=
  fun _ _ G => isIntV_mul_eventually G

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegersApproximatingRootOfUnityTwistsStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integers_approximating_root_of_unity_twists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ (τ : E →+* ℂ) (h : ℕ), 0 < h → ∀ (lab : ZMod h → (E →+* ℂ)), (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) → ∀ z : X.C, z ^ (p ^ h - 1) = 1 → (∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1) → ∀ r : ℝ, ∃ a : 𝓞 E, (∀ s, (r : WithTop ℝ) ≤ vX_vp X (embX io X (lab s) a - z ^ p ^ s.val)) ∧ ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a) := by
  first | exact @GlobalTheory.PrimePart.exists_approx_root_twists | exact GlobalTheory.PrimePart.exists_approx_root_twists | (intros; apply GlobalTheory.PrimePart.exists_approx_root_twists <;> assumption)
end

