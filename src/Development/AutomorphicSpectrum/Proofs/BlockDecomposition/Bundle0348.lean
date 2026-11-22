import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0332
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformCasimirRealStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosh_transform_casimir_real : ∀ (n : ℕ) (χ : Inf n) (g : ℝ → ℝ) (T : ℝ), IsHerm χ → IsBump g T → conj (coshT g (cas χ)) = coshT g (cas χ) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | exact GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conj_coshT_cas <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupMemRelS
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

section Per
variable {K : Type} [Field K] {W Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Y}

theorem rs_topIso {V V' : Y.Opens} (h : V' ≤ V) (x : Γ(V, ⊤)) :
    rs h (V.topIso.hom.hom x) = V'.topIso.hom.hom ((Y.homOfLE h).appTop.hom x) := by
  rw [Scheme.homOfLE_appTop]
  simp only [rs, Scheme.Opens.topIso_hom, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

def kerI (q : Y ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Y) (V : Y.Opens) : Ideal (Sec q V) := RingHom.ker (i.app V).hom

theorem one_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b j : ℕ)
    (hj : j ≠ b) : Subsingleton ((RC (G q b) P hQ).H j) := by
  subst hP
  exact (hAR K W Y q i hQ V d d' hc hc' b).1 j hj

theorem inj_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b : ℕ)
    (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (hE : IsOm q V b E) :
    Function.Injective ((incl (G q b) P hQ).mapH b) := by
  subst hP
  exact ((hAR K W Y q i hQ V d d' hc hc' b).2 E hE (incl (G q b) (inU q V) hQ) fun _ _ => rfl).1

theorem range_P [CharZero K] [IsClosedImmersion i] (hAR : AffRel) (hQ : Cosieve (On q i)) {V : Y.Opens} {P : ObjectProperty (Thick (smFun Y q))}
    (hP : P = inU q V) {d d' : ℕ} (hc : Nonempty (Coord q V d)) (hc' : Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d')) (b : ℕ)
    (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (hE : IsOm q V b E) (ω : Om K (Sec q V) b) :
    castH (G q b) hP b (E ω) ∈ LinearMap.range ((incl (G q b) P hQ).mapH b) ↔
      ω ∈ relOm K (kerI q i V) b := by
  subst hP
  exact ((hAR K W Y q i hQ V d d' hc hc' b).2 E hE (incl (G q b) (inU q V) hQ) fun _ _ => rfl).2 ω

theorem pull_P {V V' : Y.Opens} {P P' : ObjectProperty (Thick (smFun Y q))} (hP : P = inU q V) (hP' : P' = inU q V') (k : P' ≤ P)
    (b : ℕ) (E : Om K (Sec q V) b →ₗ[K] HV q V b b) (E' : Om K (Sec q V') b →ₗ[K] HV q V' b b)
    (φ : Om K (Sec q V) b →ₗ[K] Om K (Sec q V') b)
    (h : ∀ (k' : inU q V' ≤ inU q V) ω, (resU (G q b) k').pull b (E ω) = E' (φ ω)) (ω : Om K (Sec q V) b) :
    (resU (G q b) k).pull b (castH (G q b) hP b (E ω)) = castH (G q b) hP' b (E' (φ ω)) := by
  subst hP hP'
  exact h k ω

theorem cup_P (hFL : FormLaws) (hFU : FormUniq) (hFC : FormCup) {V : Y.Opens} {P U₁ U₂ : ObjectProperty (Thick (smFun Y q))} (hP : P = inU q V)
    (k₁ : P ≤ U₁) (k₂ : P ≤ U₂) (β₁ : CH.Cn (U₁.ι ⋙ G q 1) 1) (β₂ : CH.Cn (U₂.ι ⋙ G q 1) 1) {a : ℕ}
    (E₂ : Om K (Sec q V) a →ₗ[K] HV q V a a) (E₃ : Om K (Sec q V) (a + 1) →ₗ[K] HV q V (a + 1) (a + 1))
    (h₂ : IsOm q V a E₂) (h₃ : IsOm q V (a + 1) E₃) (g₁ t : Sec q V)
    (hf : ∀ (k₁' : inU q V ≤ U₁) (k₂' : inU q V ≤ U₂), ∃ hz, IsForm q V (a := 1) g₁ ![t]
      ((CH.cx ((inU q V).ι ⋙ G q 1)).cls ((resU (G q 1) k₁').pullC 1 β₁ - (resU (G q 1) k₂').pullC 1 β₂) hz))
    (w : Om K (Sec q V) a →ₗ[Sec q V] Om K (Sec q V) (a + 1))
    (hw : ∀ g₀ (g : Fin a → Sec q V), w (form K g₀ g) = form K g₀ (Fin.cons t g))
    (y : CH.Cn (P.ι ⋙ G q a) a) (hy : CH.d _ a y = 0) (ω : Om K (Sec q V) a)
    (hcls : (CH.cx _).cls y hy = castH (G q a) hP a (E₂ ω))
    (hz : CH.d (P.ι ⋙ G q (a + 1)) (a + 1) ((pairU (grOk (smFun Y q) (Nat.add_comm 1 a)).pair P).cupC (Nat.add_comm 1 a)
      ((resU (G q 1) k₁).pullC 1 β₁ - (resU (G q 1) k₂).pullC 1 β₂) y) = 0) :
    (CH.cx (P.ι ⋙ G q (a + 1))).cls ((pairU (grOk (smFun Y q) (Nat.add_comm 1 a)).pair P).cupC (Nat.add_comm 1 a)
      ((resU (G q 1) k₁).pullC 1 β₁ - (resU (G q 1) k₂).pullC 1 β₂) y) hz =
      castH (G q (a + 1)) hP (a + 1) (E₃ (g₁ • w ω)) := by
  subst hP
  obtain ⟨hb, hform⟩ := hf k₁ k₂
  exact cup_form hFL hFU hFC E₂ E₃ h₂ h₃ g₁ t _ hb hform w hw y hy ω hcls hz

theorem cup_mem_relS {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {Q : ObjectProperty C} (hQ : Cosieve Q) {p n m : ℕ} (h : p + n = m) (b : CH.Cn F₁ p) (x : CH.Cn F₂ n) (hx : x ∈ relS F₂ Q n) :
    P.cupC h b x ∈ relS F₃ Q m := by
  intro s hs
  have hx' : x ((CH.back_mono h).functor ⋙ s) = 0 := hx _ (hQ (s.map (homOfLE (Fin.zero_le _))) hs)
  change P.μ _ _ (CH.term F₂ s x (CH.back h) (CH.back_mono h)) = 0
  unfold CH.term
  rw [hx', map_zero, map_zero]

end Per

end GlobalTheory.CompanionTheory.RelKill
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisGStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degBasis_of_degBasisG' : DegBasisG → DegBasis := by
  first | exact @GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG | exact GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG | (intros; apply GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneralStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_basis_general : WedgeF → WedgeI → MulF → MulI → LogAbsBasic → FinSupp → DegBasisG := by
  first | exact @GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | exact GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of | (intros; apply GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasisStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_bounded_of_basis : WedgeF → WedgeI → MulF → MulI → SzFin → FinSupp → LogAbsBasic → DegBasisG → DegBdd := by
  first | exact @GlobalTheory.CompanionTheory.DegBound.degBdd_of | exact GlobalTheory.CompanionTheory.DegBound.degBdd_of | (intros; apply GlobalTheory.CompanionTheory.DegBound.degBdd_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentityStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_pairing_identity : WedgeF → WedgeI → MulF → MulI → PairF → PairI → SzFin → FinSupp → LogAbsBasic → ConjPlaces → DegBasisG → Radical → DegPairing := by
  first | exact @GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of | exact GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of | (intros; apply GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspaceStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_rational_subspace : DegBasisG → DegRat := by
  first | exact @GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG | exact GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG | (intros; apply GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBoundStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_submodule_bound : WedgeF → WedgeI → WedgeSub → FinSupp → DegBasisG → TwoBases → DegSubmod := by
  first | exact @GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | exact GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of | (intros; apply GlobalTheory.CompanionTheory.DegreeSubmod.degSubmod_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslationStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_under_translation : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  first | exact @GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | exact GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | (intros; apply GlobalTheory.CompanionTheory.DegMoveProof.degMove_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetBlockMatrixStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_block_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (w w' : Equiv.Perm (Fin N)), permGL k w' ∈ doubleCoset (permGL k w) (blockUpper k N β : Set (GL (Fin N) k)) (blockUpper k N γ) ↔ ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w'.symm x) = j).card) := by
  first | exact @GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card | exact GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card | (intros; apply GlobalTheory.CompanionTheory.GeoCell.permGL_mem_doubleCoset_iff_card <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTermOfIsotropicStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_term_of_isotropic : OnlyIsotropic → EllTerm := by
  first | exact @GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic | exact GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic | (intros; apply GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfRight
section
noncomputable section

open NumberField Matrix
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped ComplexConjugate ComplexOrder

namespace GlobalTheory.CompanionTheory.NonEll

variable {n : ℕ}

def formB (D : GL (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  star x ⬝ᵥ ((D⁻¹ : GL (Fin n) ℂ).val *ᵥ y)

def nrmC (D : GL (Fin n) ℂ) : GL (Fin n) ℂ := D * thetaR (starRingEnd ℂ) n D

theorem mem_perpD_iff (D : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ perpD (starRingEnd ℂ) D W ↔ ∀ x ∈ W, formB D x y = 0 := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have hiD : (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 := by simp
  constructor
  · rintro hy x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
    have := hu x hx
    simpa [formB, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hiD, dotProduct] using this
  · intro h
    refine Submodule.mem_map.2 ⟨(D⁻¹ : GL (Fin n) ℂ).val *ᵥ y, fun x hx => ?_, ?_⟩
    · simpa [formB, dotProduct] using h x hx
    · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDi]

theorem formB_nrm (D : GL (Fin n) ℂ) (x y : Fin n → ℂ) :
    formB D ((nrmC D).val *ᵥ x) ((nrmC D).val *ᵥ y) = formB D x y := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have hiD : (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 := by simp
  have hG : (nrmC D).val = D.val * ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ := by
    simp only [nrmC, Units.val_mul, thetaR_val]
    rfl
  have hH : ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ * (D.val)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hDi, Matrix.conjTranspose_one]
  have hK : (nrmC D).valᴴ * (D⁻¹ : GL (Fin n) ℂ).val * (nrmC D).val = (D⁻¹ : GL (Fin n) ℂ).val := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc _ = (D⁻¹ : GL (Fin n) ℂ).val * (D.val)ᴴ * ((D⁻¹ : GL (Fin n) ℂ).val * D.val) *
          ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ := by simp only [Matrix.mul_assoc]
      _ = (D⁻¹ : GL (Fin n) ℂ).val * ((D.val)ᴴ * ((D⁻¹ : GL (Fin n) ℂ).val)ᴴ) := by
          rw [hiD, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
          rw [← Matrix.conjTranspose_mul, hiD, Matrix.conjTranspose_one, Matrix.mul_one]
  unfold formB
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hK]

theorem formB_smul_left (D : GL (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    formB D (c • x) y = conj c * formB D x y := by
  simp [formB, dotProduct, Finset.mul_sum, mul_assoc]

theorem formB_smul_right (D : GL (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    formB D x (c • y) = c * formB D x y := by
  simp [formB, Matrix.mulVec_smul, dotProduct_smul]

theorem formB_add_left (D : GL (Fin n) ℂ) (x x' y : Fin n → ℂ) :
    formB D (x + x') y = formB D x y + formB D x' y := by
  simp [formB, star_add, add_dotProduct]

theorem formB_add_right (D : GL (Fin n) ℂ) (x y y' : Fin n → ℂ) :
    formB D x (y + y') = formB D x y + formB D x y' := by
  simp [formB, Matrix.mulVec_add, dotProduct_add]

theorem formB_zero_left (D : GL (Fin n) ℂ) (y : Fin n → ℂ) : formB D 0 y = 0 := by simp [formB]

theorem formB_zero_right (D : GL (Fin n) ℂ) (x : Fin n → ℂ) : formB D x 0 = 0 := by simp [formB]

theorem eq_zero_of_left (D : GL (Fin n) ℂ) (x : Fin n → ℂ) (h : ∀ y, formB D x y = 0) : x = 0 := by
  have hDi : D.val * (D⁻¹ : GL (Fin n) ℂ).val = 1 := by simp
  have h1 := h (D.val *ᵥ x)
  simp only [formB, Matrix.mulVec_mulVec] at h1
  rw [show (D⁻¹ : GL (Fin n) ℂ).val * D.val = 1 by simp, Matrix.one_mulVec] at h1
  exact dotProduct_star_self_eq_zero.1 h1

theorem eq_zero_of_right (D : GL (Fin n) ℂ) (y : Fin n → ℂ) (h : ∀ x, formB D x y = 0) : y = 0 := by
  have h1 := h ((D⁻¹ : GL (Fin n) ℂ).val *ᵥ y)
  have h2 : (D⁻¹ : GL (Fin n) ℂ).val *ᵥ y = 0 := dotProduct_star_self_eq_zero.1 h1
  have h3 := congrArg (fun w => D.val *ᵥ w) h2
  simpa [Matrix.mulVec_mulVec] using h3

abbrev endN (D : GL (Fin n) ℂ) : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' (nrmC D).val

theorem eigen_pair (D : GL (Fin n) ℂ) {μ ν : ℂ} {x y : Fin n → ℂ} (hx : x ∈ (endN D).eigenspace μ)
    (hy : y ∈ (endN D).eigenspace ν) (h : conj μ * ν ≠ 1) : formB D x y = 0 := by
  have e1 : (nrmC D).val *ᵥ x = μ • x := by simpa using Module.End.mem_eigenspace_iff.1 hx
  have e2 : (nrmC D).val *ᵥ y = ν • y := by simpa using Module.End.mem_eigenspace_iff.1 hy
  have := formB_nrm D x y
  rw [e1, e2, formB_smul_left, formB_smul_right, ← mul_assoc] at this
  by_contra h0
  exact h (mul_right_cancel₀ h0 (by rw [this, one_mul]))

def eigSum (D : GL (Fin n) ℂ) (P : ℂ → Prop) : Submodule ℂ (Fin n → ℂ) :=
  ⨆ μ : {μ : ℂ // P μ}, (endN D).eigenspace μ

theorem eigen_le (D : GL (Fin n) ℂ) {P : ℂ → Prop} {μ : ℂ} (h : P μ) :
    (endN D).eigenspace μ ≤ eigSum D P :=
  le_iSup (fun μ : {μ : ℂ // P μ} => (endN D).eigenspace μ) ⟨μ, h⟩

theorem eigSum_orth (D : GL (Fin n) ℂ) {P Q : ℂ → Prop} (h : ∀ μ ν, P μ → Q ν → conj μ * ν ≠ 1)
    {x y : Fin n → ℂ} (hx : x ∈ eigSum D P) (hy : y ∈ eigSum D Q) : formB D x y = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem μ x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem ν y hy => exact eigen_pair D hx hy (h _ _ μ.2 ν.2)
    | zero => exact formB_zero_right D x
    | add a b _ _ ha hb => rw [formB_add_right, ha, hb, add_zero]
  | zero => exact formB_zero_left D y
  | add a b _ _ ha hb => rw [formB_add_left, ha, hb, add_zero]

theorem iSup_eigen (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) :
    ⨆ μ, (endN D).eigenspace μ = ⊤ := by
  have hss : (endN D).IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree ?_
    rw [← Matrix.charpoly_toLin']
    exact LinearMap.aeval_self_charpoly _
  have h1 := Module.End.iSup_maxGenEigenspace_eq_top (endN D)
  simpa only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1

theorem eigSum_sup (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {P Q : ℂ → Prop}
    (h : ∀ μ, P μ ∨ Q μ) : eigSum D P ⊔ eigSum D Q = ⊤ := by
  rw [eq_top_iff, ← iSup_eigen D hs]
  refine iSup_le fun μ => ?_
  rcases h μ with h | h
  · exact (eigen_le D h).trans le_sup_left
  · exact (eigen_le D h).trans le_sup_right

theorem perpD_eigSum (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {P Q R P' : ℂ → Prop}
    (hPQ : ∀ μ ν, P μ → Q ν → conj μ * ν ≠ 1) (hQR : ∀ μ, Q μ ∨ R μ) (hPP : ∀ μ, P μ ∨ P' μ)
    (hPR : ∀ μ ν, P' μ → R ν → conj μ * ν ≠ 1) :
    perpD (starRingEnd ℂ) D (eigSum D P) = eigSum D Q := by
  apply le_antisymm
  · intro y hy
    rw [mem_perpD_iff] at hy
    have hy' : y ∈ eigSum D Q ⊔ eigSum D R := by rw [eigSum_sup D hs hQR]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
    have hb0 : b = 0 := by
      refine eq_zero_of_right D b fun x => ?_
      have hx : x ∈ eigSum D P ⊔ eigSum D P' := by rw [eigSum_sup D hs hPP]; trivial
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
      have h1 : formB D p b = 0 := by
        have := hy p hp
        rwa [formB_add_right, eigSum_orth D hPQ hp ha, zero_add] at this
      rw [formB_add_left, h1, eigSum_orth D hPR hq hb, add_zero]
    rw [hb0, add_zero]
    exact ha
  · intro y hy
    rw [mem_perpD_iff]
    exact fun x hx => eigSum_orth D hPQ hx hy

theorem conj_mul_ne {μ ν : ℂ} (h : ‖μ‖ * ‖ν‖ ≠ 1) : conj μ * ν ≠ 1 := by
  intro e
  have := congrArg norm e
  rw [norm_mul, Complex.norm_conj, norm_one] at this
  exact h this

theorem locFlag (D : GL (Fin n) ℂ) (hs : (nrmC D).val.charpoly.Separable) {z : ℂ}
    (hz : (nrmC D).val.charpoly.IsRoot z) (hz1 : ‖z‖ ≠ 1) :
    ∃ W₁ W₂ : Submodule ℂ (Fin n → ℂ), W₁ ≠ ⊥ ∧ W₁ ≤ W₂ ∧ perpD (starRingEnd ℂ) D W₁ = W₂ ∧
      perpD (starRingEnd ℂ) D W₂ = W₁ := by
  have n1 : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 1 < a → 1 ≤ b → a * b ≠ 1 := fun {a b} _ _ ha hb => by nlinarith
  have n2 : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a < 1 → b ≤ 1 → a * b ≠ 1 := fun {a b} h0 h1 ha hb => by nlinarith
  have p1 : perpD (starRingEnd ℂ) D (eigSum D (fun μ => 1 < ‖μ‖)) = eigSum D (fun μ => 1 ≤ ‖μ‖) :=
    perpD_eigSum D hs (R := fun μ => ‖μ‖ < 1) (P' := fun μ => ‖μ‖ ≤ 1)
      (fun μ ν hμ hν => conj_mul_ne (n1 (norm_nonneg _) (norm_nonneg _) hμ hν))
      (fun μ => le_or_gt 1 ‖μ‖) (fun μ => (lt_or_ge 1 ‖μ‖))
      (fun μ ν hμ hν => conj_mul_ne (by
        rw [mul_comm]; exact n2 (norm_nonneg _) (norm_nonneg _) hν hμ))
  have p2 : perpD (starRingEnd ℂ) D (eigSum D (fun μ => 1 ≤ ‖μ‖)) = eigSum D (fun μ => 1 < ‖μ‖) :=
    perpD_eigSum D hs (R := fun μ => ‖μ‖ ≤ 1) (P' := fun μ => ‖μ‖ < 1)
      (fun μ ν hμ hν => conj_mul_ne (by
        rw [mul_comm]; exact n1 (norm_nonneg _) (norm_nonneg _) hν hμ))
      (fun μ => lt_or_ge 1 ‖μ‖) (fun μ => le_or_gt 1 ‖μ‖)
      (fun μ ν hμ hν => conj_mul_ne (n2 (norm_nonneg _) (norm_nonneg _) hμ hν))
  refine ⟨_, _, ?_, ?_, p1, p2⟩
  · intro hbot
    have hev : (endN D).HasEigenvalue z := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hz
    obtain ⟨e, hee⟩ := hev.exists_hasEigenvector
    have he := hee.1
    have he0 := hee.2
    rcases lt_or_gt_of_ne hz1 with hlt | hgt
    · refine he0 (eq_zero_of_left D e fun y => ?_)
      have hy : y ∈ ⨆ μ, (endN D).eigenspace μ := by rw [iSup_eigen D hs]; trivial
      induction hy using Submodule.iSup_induction' with
      | mem ν y hy =>
        by_cases hν : 1 < ‖ν‖
        · have : y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hbot ▸ eigen_le D hν hy
          rw [(Submodule.mem_bot ℂ).1 this]
          exact formB_zero_right D e
        · exact eigen_pair D he hy (conj_mul_ne (n2 (norm_nonneg _) (norm_nonneg _) hlt (not_lt.1 hν)))
      | zero => exact formB_zero_right D e
      | add a b _ _ ha hb => rw [formB_add_right, ha, hb, add_zero]
    · have : e ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hbot ▸ eigen_le D hgt he
      exact he0 ((Submodule.mem_bot ℂ).1 this)
  · exact iSup_le fun μ => eigen_le D (le_of_lt μ.2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjE_emb (σ : E →+* ℂ) (x : E) : σ (conjE E x) = conj (σ x) :=
  IsCMField.complexEmbedding_complexConj E σ x

theorem nrmC_locGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    (nrmC (locGL v d)).val = (nrm d).val.map v.embedding := by
  have h1 : ((locGL v d)⁻¹ : GL (Fin n) ℂ).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := by
    rw [← map_inv]; rfl
  simp only [nrmC, nrm, Units.val_mul, thetaR_val, Matrix.map_mul]
  rw [h1]
  congr 1
  ext i j
  simp [conjE_emb]

theorem nonEllFlag : PositivityTheory.Rg.BcB.D4.NonEllFlag := by
  intro E _ _ _ n d hreg hell
  have hnot : ∃ (τ : E →+* ℂ) (z : ℂ), ((nrm d).val.charpoly.map τ).IsRoot z ∧ ‖z‖ ≠ 1 := by
    by_contra hno
    push_neg at hno
    exact hell ⟨hreg, fun τ z hz => hno τ z hz⟩
  obtain ⟨τ, z, hz, hz1⟩ := hnot
  refine ⟨InfinitePlace.mk τ, ?_⟩
  set v := InfinitePlace.mk τ with hv
  have hcp : (nrmC (locGL v d)).val.charpoly = (nrm d).val.charpoly.map v.embedding := by
    rw [nrmC_locGL, Matrix.charpoly_map]
  have hs : (nrmC (locGL v d)).val.charpoly.Separable := by
    rw [hcp]; exact Polynomial.Separable.map hreg
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · exact locFlag (locGL v d) hs (z := z) (by rw [hcp, hv, h]; exact hz) hz1
  · refine locFlag (locGL v d) hs (z := conj z) ?_ (by rwa [Complex.norm_conj])
    rw [hcp, hv, h]
    have e : (nrm d).val.charpoly.map (ComplexEmbedding.conjugate τ) =
        ((nrm d).val.charpoly.map τ).map (starRingEnd ℂ) := by
      rw [Polynomial.map_map]; rfl
    rw [e]
    exact Polynomial.IsRoot.map hz

end GlobalTheory.CompanionTheory.NonEll

end
end

