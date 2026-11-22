import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolicStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = GlobalTheory.JSW.psiLoc w x) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS E (m + 1) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  first | exact @GlobalTheory.JSW.CutProd.cut_prod_mirS | exact GlobalTheory.JSW.CutProd.cut_prod_mirS | (intros; apply GlobalTheory.JSW.CutProd.cut_prod_mirS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjByCarryingUnitMemPositiveSimilitudeFormGroup
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem pair_conj_mem_grp : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (B y : G.Cˣ) (s : ℚ), 0 < s → 0 < ((P.c : ℚˣ) : ℚ) → (P.β : G.C) = algebraMap ℚ G.C s * (y * B * sh G y) → ((y⁻¹ * P.γ * y, P.c) : G.Cˣ × ℚˣ) ∈ grp G B := by
  intro p _ G P B y s hs hc hβ
  refine ⟨?_, hc⟩
  change ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) * B * sh G ((y⁻¹ * P.γ * y : G.Cˣ) : G.C) = algebraMap ℚ G.C (P.c : ℚ) * B
  have hmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← hmul, Units.inv_mul]; simp [sh]
  have hs0 : s ≠ 0 := hs.ne'
  have hβ' : (P.β : G.C) = s • ((y : G.C) * B * sh G y) := by rw [hβ, Algebra.smul_def]
  have hY : (y : G.C) * B * sh G y = s⁻¹ • (P.β : G.C) := by
    rw [hβ', smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hsim : (P.γ : G.C) * P.β * sh G P.γ = (P.c : ℚ) • (P.β : G.C) := by
    rw [P.sim, Algebra.smul_def]
  rw [Units.val_mul, Units.val_mul, hmul, hmul, ← Algebra.smul_def]
  calc ((y⁻¹ : G.Cˣ) : G.C) * P.γ * y * B * (sh G y * (sh G P.γ * sh G ((y⁻¹ : G.Cˣ) : G.C)))
      = ((y⁻¹ : G.Cˣ) : G.C) * (P.γ * ((y : G.C) * B * sh G y) * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C) := by
        simp only [mul_assoc]
    _ = s⁻¹ • (((y⁻¹ : G.Cˣ) : G.C) * ((P.γ : G.C) * P.β * sh G P.γ) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hY]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ)) • (((y⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
        rw [hsim, mul_smul]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = (s⁻¹ * (P.c : ℚ) * s) • ((((y⁻¹ : G.Cˣ) : G.C) * y) * B * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
        rw [hβ', mul_smul (s⁻¹ * (P.c : ℚ)) s]; simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = (P.c : ℚ) • (B : G.C) := by
        rw [Units.inv_mul, e, one_mul, mul_one, mul_comm (s⁻¹) _, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFormsRescale
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

section Abstract

variable {K S V W W' : Type} [Field K] [AddCommGroup S] [Module K S] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W']

theorem rescale_span_eq {ι κ : Type} [Finite κ] (K0 : Subfield K) (f : Module.Basis ι K V) (b : Module.Basis κ K V)
    (h : ∀ i j, b.repr (f i) j ∈ K0) : Submodule.span K0 (Set.range f) = Submodule.span K0 (Set.range b) := by
  haveI : Finite ι := Finite.of_equiv κ (b.indexEquiv f)
  haveI := Fintype.ofFinite ι
  haveI := Fintype.ofFinite κ
  haveI : FiniteDimensional K0 (Submodule.span K0 (Set.range b)) := FiniteDimensional.span_of_finite K0 (Set.finite_range b)
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (b.mem_span_iff_repr_mem K0 (f i)).2 fun j => ⟨⟨_, h i j⟩, rfl⟩
  · rw [finrank_span_eq_card (f.linearIndependent.restrict_scalars' K0),
      finrank_span_eq_card (b.linearIndependent.restrict_scalars' K0)]
    exact Fintype.card_congr (f.indexEquiv b)

theorem rescale_mem {ι κ : Type} [Finite κ] (K0 : Subfield K) (bS : Module.Basis ι K S) (b : Module.Basis κ K V)
    (e e' : S ≃ₗ[K] V) (h : ∀ i j, b.repr (e (bS i)) j ∈ K0) (h' : ∀ i j, b.repr (e' (bS i)) j ∈ K0) (a : κ) :
    e' (e.symm (b a)) ∈ Submodule.span K0 (Set.range b) := by
  have h1 := rescale_span_eq K0 (bS.map e) b h
  have h2 := rescale_span_eq K0 (bS.map e') b h'
  have h3 : b a ∈ Submodule.span K0 (Set.range (bS.map e)) := h1 ▸ Submodule.subset_span ⟨a, rfl⟩
  rw [← h2]
  generalize b a = x at h3
  induction h3 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Subfield.smul_def, map_smul, map_smul]
    exact Submodule.smul_mem _ r hx

theorem rescale_pair [StarRing K] {κ : Type} (b : κ → V) (σ : K →+* ℂ) (c₁ : V →ₛₗ[σ] W)
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pair (b a) (b a')))
    {x y : V} (hx : x ∈ Submodule.span (Formalism.DivisionValues.cmMax K) (Set.range b))
    (hy : y ∈ Submodule.span (Formalism.DivisionValues.cmMax K) (Set.range b)) : inner ℂ (c₁ x) (c₁ y) = σ (pair x y) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a', rfl⟩ := hy
      exact hp a a'
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, inner_add_right, hx, hy, map_add, map_add]
    | smul r x _ hx =>
      rw [Subfield.smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hx, map_smul, smul_eq_mul, map_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, inner_add_left, hx, hy, map_add, LinearMap.add_apply, map_add]
  | smul r x _ hx =>
    rw [Subfield.smul_def, LinearMap.map_smulₛₗ, inner_smul_left, hx, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, ← r.2 σ]
    rfl

theorem rescale_inj {κ : Type} [Finite κ] (b : Module.Basis κ K V) (σ : K →+* ℂ) (c : V →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun a => c (b a)) : Function.Injective c := by
  haveI := Fintype.ofFinite κ
  refine (injective_iff_map_eq_zero c).2 fun x hx => ?_
  rw [← b.sum_repr x, map_sum] at hx
  simp only [LinearMap.map_smulₛₗ] at hx
  have := Fintype.linearIndependent_iff.1 h _ hx
  exact b.ext_elem fun a => by simpa using this a

theorem rescale_span_top {κ : Type} [Finite κ] (b : Module.Basis κ K V) (σ : K →+* ℂ) (c : V →ₛₗ[σ] W) (φ : V ≃ₗ[K] V)
    (h : Submodule.span ℂ (Set.range fun a => c (b a)) = ⊤) :
    Submodule.span ℂ (Set.range fun a => c (φ (b a))) = ⊤ := by
  haveI := Fintype.ofFinite κ
  refine top_le_iff.1 (h ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨a, rfl⟩
  have : b a = ∑ k, b.repr (φ.symm (b a)) k • φ (b k) := by
    conv_lhs => rw [← φ.apply_symm_apply (b a), ← b.sum_repr (φ.symm (b a))]
    simp only [map_sum, map_smul]
  change c (b a) ∈ Submodule.span ℂ _
  rw [this, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem rescale_indep {κ : Type} [Finite κ] (u v : κ → W) (hi : LinearIndependent ℂ u)
    (hu : Submodule.span ℂ (Set.range u) = ⊤) (hv : Submodule.span ℂ (Set.range v) = ⊤) : LinearIndependent ℂ v := by
  haveI := Fintype.ofFinite κ
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge
    (Module.finrank_eq_card_basis (Module.Basis.mk hi hu.ge)).symm

theorem rescale_abstract [StarRing K] {ι κ : Type} [Finite κ] (bS : Module.Basis ι K S) (b : Module.Basis κ K V)
    (τ σ : K →+* ℂ) (p : S → W) (c0 c0' : V →ₛₗ[τ] W) (pair : V →ₗ⋆[K] V →ₗ[K] K) (q : S → S → K)
    (e e' : S ≃ₗ[K] V) (h : ∀ i j, b.repr (e (bS i)) j ∈ Formalism.DivisionValues.cmMax K)
    (h' : ∀ i j, b.repr (e' (bS i)) j ∈ Formalism.DivisionValues.cmMax K)
    (hc : ∀ x, p x = c0 (e x)) (hc' : ∀ x, p x = c0' (e' x))
    (hq : ∀ x y, pair (e x) (e y) = q x y) (hq' : ∀ x y, pair (e' x) (e' y) = q x y)
    (hi' : LinearIndependent ℂ fun a => c0' (b a)) (c₁ : V →ₛₗ[σ] W')
    (hi : LinearIndependent ℂ fun a => c₁ (b a)) (hs : Submodule.span ℂ (Set.range fun a => c₁ (b a)) = ⊤)
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pair (b a) (b a'))) :
    ∃ c₁' : V →ₛₗ[σ] W', (LinearIndependent ℂ fun a => c₁' (b a)) ∧
      Submodule.span ℂ (Set.range fun a => c₁' (b a)) = ⊤ ∧
      (∀ a a', inner ℂ (c₁' (b a)) (c₁' (b a')) = σ (pair (b a) (b a'))) ∧
      (∀ v', ∃ v, c0' v' = c0 v ∧ c₁ v' = c₁' v) ∧
      ∀ (r : V → V) (ρ : W → W) (ρ' : W' → W'), (∀ v, c0 (r v) = ρ (c0 v)) → (∀ v, c0' (r v) = ρ (c0' v)) →
        (∀ v, c₁ (r v) = ρ' (c₁ v)) → ∀ v, c₁' (r v) = ρ' (c₁' v) := by
  have hφ : ∀ v, c0' (e' (e.symm v)) = c0 v := fun v => by rw [← hc', hc, e.apply_symm_apply]
  have hs' := rescale_span_top b σ c₁ (e.symm.trans e') hs
  refine ⟨c₁.comp (e.symm.trans e').toLinearMap, rescale_indep _ _ hi hs hs', hs', fun a a' => ?_, fun v' => ?_,
    fun r ρ ρ' h0 h0' h1 v => ?_⟩
  · refine (rescale_pair b σ c₁ pair hp (rescale_mem _ bS b e e' h h' a) (rescale_mem _ bS b e e' h h' a')).trans ?_
    rw [hq', ← hq, e.apply_symm_apply, e.apply_symm_apply]
  · refine ⟨e (e'.symm v'), ?_, ?_⟩
    · rw [← hφ, e.symm_apply_apply, e'.apply_symm_apply]
    · simp
  · have : e' (e.symm (r v)) = r (e' (e.symm v)) := rescale_inj b τ c0' hi' (by rw [hφ, h0, h0', hφ])
    change c₁ (e' (e.symm (r v))) = ρ' (c₁ (e' (e.symm v)))
    rw [this, h1]

end Abstract

end GlobalTheory.GalLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFrameMemUH
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar

theorem conjFrame_mem_UH : ∀ (p q n : ℕ), p + q = n → ∀ (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), (Aᴴ * Formalism.UG.Jpq p q * A : Matrix (Fin n) (Fin n) ℂ) = Gm → IsUnit Gm.det → ∀ b : UpqT p q, conjFrame Gm A (UpqT.mat b) ∈ Formalism.QuantumDeterminants.UH Gm := by
  intro p q n hn Gm A hA hG b
  have hJ : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]
  have h1 : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul _ hG
  have hb : (UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b = Formalism.UG.Jpq p q := b.2
  have hl : (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by rw [Matrix.mul_assoc, hA, h1]
  have e : Fin n ≃ Fin p ⊕ Fin q := (finCongr hn.symm).trans finSumFinEquiv.symm
  have hr : A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  have hc : A * conjFrame Gm A (UpqT.mat b) = UpqT.mat b * A := by
    have : A * conjFrame Gm A (UpqT.mat b) = A * (Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * (UpqT.mat b * A) := by
      simp only [conjFrame, Matrix.mul_assoc]
    rw [this, hr, Matrix.one_mul]
  change (conjFrame Gm A (UpqT.mat b))ᴴ * Gm * conjFrame Gm A (UpqT.mat b) = Gm
  generalize conjFrame Gm A (UpqT.mat b) = C at hc
  calc Cᴴ * Gm * C = (A * C)ᴴ * Formalism.UG.Jpq p q * (A * C) := by
        rw [← hA]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * ((UpqT.mat b)ᴴ * Formalism.UG.Jpq p q * UpqT.mat b) * A := by
        rw [hc]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Gm := by rw [hb, hA]

end GlobalTheory.AdelicScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemBlockUpperUnipotentRadicalStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_blockUpperUnipotentRadical : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b),
  ∀ p ∈ GlobalTheory.OrbDesc.blockPar (K := K) e, ∀ n ∈ GlobalTheory.OrbDesc.blockUni e, p * n * p⁻¹ ∈ GlobalTheory.OrbDesc.blockUni e := by
  first | exact @GlobalTheory.OrbDesc.blockUni_conj_mem | exact GlobalTheory.OrbDesc.blockUni_conj_mem | (intros; apply GlobalTheory.OrbDesc.blockUni_conj_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_models_multiplicity_equal : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q (fun P => (Sg P).map (starRingEnd ℂ)) : Submodule ℂ (MMap M')) := by
  first | exact @GlobalTheory.ConjDim.conj_rank | exact GlobalTheory.ConjDim.conj_rank | (intros; apply GlobalTheory.ConjDim.conj_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem grp_factor_eq_of_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 := by
  intro p _ G β y y₀ c hyc
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  haveI : Nontrivial G.C := inferInstance
  set d : G.C → ℚ := fun a => LinearMap.det (LinearMap.mulLeft ℚ a) with hd
  have dmul : ∀ a b, d (a * b) = d a * d b := by
    intro a b; simp only [hd, LinearMap.mulLeft_mul, LinearMap.det_comp]
  have done : d 1 = 1 := by simp [hd, LinearMap.mulLeft_one]
  have dsc : ∀ s : ℚ, d (algebraMap ℚ G.C s) = s ^ Module.finrank ℚ G.C := by
    intro s
    have : LinearMap.mulLeft ℚ (algebraMap ℚ G.C s) = s • LinearMap.id := by
      ext x; simp [Algebra.smul_def]
    simp only [hd, this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have dunit : ∀ u : G.Cˣ, d (u : G.C) * d ((u⁻¹ : G.Cˣ) : G.C) = 1 := by
    intro u; rw [← dmul, Units.mul_inv, done]
  have shmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by simp [sh]
  have dsh_conj : d (sh G (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C))) =
      d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    have e : d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C)) = 1 := by
      rw [← dmul, ← shmul, Units.mul_inv, shone, done]
    rw [shmul, shmul, dmul, dmul]
    calc d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * (d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * d (sh G (c : G.C)))
        = d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
          (d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C))) := by ring
      _ = _ := by rw [e, mul_one]
  have d_conj : d (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) =
      d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    rw [dmul, dmul]
    calc d (c : G.C) * d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)
        = d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * (d (c : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)) := by ring
      _ = _ := by rw [dunit, mul_one]
  obtain ⟨hy, hs⟩ := y.2
  obtain ⟨hy₀, hs₀⟩ := y₀.2
  have ey := congrArg d hy
  have ey₀ := congrArg d hy₀
  rw [dmul, dmul, dmul, dsc] at ey ey₀
  rw [hyc, d_conj, dsh_conj, ey₀] at ey
  have hβ : d (β : G.C) ≠ 0 := by
    intro h; have := dunit β; rw [h, zero_mul] at this; exact zero_ne_one this
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  have hpow : ((y : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C = ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C :=
    (mul_right_cancel₀ hβ ey).symm
  exact Units.ext ((pow_left_inj₀ hs.le hs₀.le hN).1 hpow)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower

namespace GlobalTheory.Proof.ConjugateTransposeMajorant

section

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem csum_eq_coord (S : CSD K) (f g : S.Forms) :
    S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) = star (fun a => S.basis.repr f a) ⬝ᵥ S.H *ᵥ fun a => S.basis.repr g a := by
  have hf : ∀ c, (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr f]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hg : ∀ c, (g : S.Cl → S.V) c = ∑ a, S.basis.repr g a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr g]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have e : ∀ c, S.pair ((f : S.Cl → S.V) c) ((g : S.Cl → S.V) c) =
      ∑ a, ∑ b, star (S.basis.repr f a) * (S.pair ((S.basis a : S.Cl → S.V) c) ((S.basis b : S.Cl → S.V) c) *
        S.basis.repr g b) := by
    intro c
    rw [hf c, hg c, map_sum S.pair, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  simp only [CSD.csum, CSD.H, e, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

omit [NumberField K] in
theorem map_conjTranspose_of_mem {m n : Type} (E : Matrix m n K) (hE : ∀ a k, E a k ∈ cmMax K) (σ : K →+* ℂ) :
    Eᴴ.map σ = (E.map σ)ᴴ := by
  ext i j
  exact hE j i σ

omit [NumberField K] [StarRing K] in
theorem map_mulVec' {m n : Type} [Fintype n] (E : Matrix m n K) (x : n → K) (σ : K →+* ℂ) :
    (fun a => σ ((E *ᵥ x) a)) = E.map σ *ᵥ fun k => σ (x k) := by
  funext a
  simp [Matrix.mulVec, dotProduct, map_sum]

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)

theorem repr_toF (x : Fin (B.dZ ℓ Z) → K) : (fun a => B.S.basis.repr (B.toF ℓ Z x) a) = B.fE ℓ Z *ᵥ x := by
  have : B.S.basis.equivFun (B.toF ℓ Z x) = B.fE ℓ Z *ᵥ x := by
    rw [BlockDat.fE, ← Matrix.mulVec_mulVec]
    exact B.S.basis.equivFun.apply_symm_apply _
  rw [← this]
  rfl

theorem HZ_eq : B.HZ ℓ Z = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.fE ℓ Z)ᴴ * B.S.H * B.fE ℓ Z) := by
  have : B.HV ℓ = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [BlockDat.HZ, this, BlockDat.fE, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem csumAt_toF (σ : K →+* ℂ) (x : Fin (B.dZ ℓ Z) → K) (u : B.S.Forms) :
    csumAt B.S σ (B.toF ℓ Z x) u = star (fun k => σ (x k)) ⬝ᵥ ((B.fE ℓ Z).map σ)ᴴ *ᵥ
      (B.S.H.map σ *ᵥ fun a => σ (B.S.basis.repr u a)) := by
  have h : (fun a => σ (B.S.basis.repr (B.toF ℓ Z x) a)) = (B.fE ℓ Z).map σ *ᵥ fun k => σ (x k) := by
    rw [← map_mulVec', ← repr_toF]
  unfold csumAt
  rw [h, Matrix.star_mulVec, Matrix.dotProduct_mulVec _ (((B.fE ℓ Z).map σ)ᴴ)]

end

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem majAt_eq_csumAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms), IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → (∀ a k, B.fE ℓ Z a k ∈ cmMax K) → (∀ (v : InfinitePlace K) x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ * csumAt B.S v.embedding (B.toF ℓ Z x) (B.toF ℓ Z y)) ∧ ∀ u : B.S.Forms, (∀ x, B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (u : B.S.Cl → B.S.V) = 0) → ∀ (σ : K →+* ℂ) x, csumAt B.S σ (B.toF ℓ Z x) u = 0 := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z hH hE
  refine ⟨fun v x y => ?_, fun u hu σ x => ?_⟩
  · have h1 : ∀ w : Fin (B.dZ ℓ Z) → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K _) v w = fun k => v.embedding (w k) := by
      intro w; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    have h2 : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y =
        star ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (x k)) ⬝ᵥ ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (y k)) := by
      simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1]
      rfl
    have h3 : (fun a => v.embedding (B.S.basis.repr (B.toF ℓ Z y) a)) =
        (B.fE ℓ Z).map v.embedding *ᵥ fun k => v.embedding (y k) := by
      rw [← map_mulVec', ← repr_toF]
    have h4 : (B.HZ ℓ Z).map v.embedding = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ •
        (((B.fE ℓ Z).map v.embedding)ᴴ * B.S.H.map v.embedding * (B.fE ℓ Z).map v.embedding) := by
      rw [← map_conjTranspose_of_mem _ hE, ← Matrix.map_mul, ← Matrix.map_mul, HZ_eq]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
    rw [h2, csumAt_toF, h3, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (hH.2 v).2, h4,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · have h0 : (B.fE ℓ Z)ᴴ *ᵥ (B.S.H *ᵥ fun a => B.S.basis.repr u a) = 0 := by
      funext k
      have := hu (Pi.single k 1)
      rw [csum_eq_coord, repr_toF, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
      have e : star (Pi.single k (1 : K) : Fin (B.dZ ℓ Z) → K) = Pi.single k 1 := by
        rw [Pi.star_single, star_one]
      rw [e, single_dotProduct, one_mul] at this
      exact this
    rw [csumAt_toF, ← map_mulVec', ← map_conjTranspose_of_mem _ hE, ← map_mulVec', h0]
    simp

end GlobalTheory.Proof.ConjugateTransposeMajorant

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem unit_conj_form_props {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β Y c : G.Cˣ) (s : ℚ) (hβ : sh G β = β)
    (h0 : (Y : G.C) * β * sh G Y = algebraMap ℚ G.C s * β)
    (h1 : ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c : G.C) * Y * ((c⁻¹ : G.Cˣ) : G.C)) =
      algebraMap ℚ G.C s * β) :
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧
    Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (Y : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
      ((β⁻¹ : G.Cˣ) : G.C) = ((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
  have shm : ∀ x z : G.C, sh G (x * z) = sh G z * sh G x := fun x z => by simp [sh]
  have shs : ∀ x : G.C, sh G (sh G x) = x := G.star_star
  have sh1 : sh G 1 = 1 := sh_one_eq G
  set u : G.C := ((c⁻¹ : G.Cˣ) : G.C) with hu
  set bi : G.C := ((β⁻¹ : G.Cˣ) : G.C) with hbi_def
  set S : G.C := algebraMap ℚ G.C s with hS
  have hA : ∀ r : G.C, u * ((c : G.C) * r) = r := fun r => by rw [← mul_assoc, hu, Units.inv_mul, one_mul]
  have hB : sh G (c : G.C) * sh G u = 1 := by rw [← shm, hu, Units.inv_mul, sh1]
  have hB' : ∀ r : G.C, sh G (c : G.C) * (sh G u * r) = r := fun r => by rw [← mul_assoc, hB, one_mul]
  have hC : ∀ r : G.C, (β : G.C) * (bi * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.mul_inv, one_mul]
  have hC' : ∀ r : G.C, bi * ((β : G.C) * r) = r := fun r => by rw [← mul_assoc, hbi_def, Units.inv_mul, one_mul]
  have hD : (β : G.C) * bi = 1 := by rw [hbi_def, Units.mul_inv]
  set shYi : G.C := sh G ((Y⁻¹ : G.Cˣ) : G.C) with hshYi
  have hE : ∀ r : G.C, sh G (Y : G.C) * (shYi * r) = r := fun r => by
    rw [← mul_assoc, hshYi, ← shm, Units.inv_mul, sh1, one_mul]
  have hE1 : sh G (Y : G.C) * shYi = 1 := by rw [hshYi, ← shm, Units.inv_mul, sh1]
  refine ⟨?_, ?_, ?_⟩
  · have hshu : IsUnit (sh G u) := ⟨⟨sh G u, sh G (c : G.C), by rw [← shm, hu, Units.mul_inv, sh1], hB⟩, rfl⟩
    exact (((Units.isUnit _).mul (Units.isUnit β)).mul hshu).mul (Units.isUnit _)
  · have h2 : (Y : G.C) * (u * β * sh G u) * sh G Y = S * (u * β * sh G u) := by
      calc (Y : G.C) * (u * β * sh G u) * sh G Y
          = u * (((c : G.C) * Y * u) * β * sh G ((c : G.C) * Y * u)) * sh G u := by
            simp only [shm, mul_assoc, hA, hB, hB', mul_one]
        _ = S * (u * β * sh G u) := by
            rw [h1, hS, ← mul_assoc, ← Algebra.commutes s u]; simp only [mul_assoc]
    have e1 : (Y : G.C) * (u * β * sh G u * bi) = S * ((u * β * sh G u) * (shYi * bi)) := by
      calc (Y : G.C) * (u * β * sh G u * bi) = ((Y : G.C) * (u * β * sh G u) * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE]
        _ = _ := by rw [h2, mul_assoc]
    have eY : (Y : G.C) = S * ((β : G.C) * (shYi * bi)) := by
      calc (Y : G.C) = ((Y : G.C) * β * sh G Y) * (shYi * bi) := by
            simp only [mul_assoc, hE, hD, mul_one]
        _ = _ := by rw [h0, mul_assoc]
    have e2 : (u * β * sh G u * bi) * (Y : G.C) = S * ((u * β * sh G u) * (shYi * bi)) := by
      rw [eY]
      calc u * β * sh G u * bi * (S * ((β : G.C) * (shYi * bi)))
          = (u * β * sh G u) * (bi * S * ((β : G.C) * (shYi * bi))) := by simp only [mul_assoc]
        _ = (u * β * sh G u) * (S * (bi * ((β : G.C) * (shYi * bi)))) := by
            rw [hS, ← Algebra.commutes s bi]; simp only [mul_assoc]
        _ = _ := by rw [hC', ← mul_assoc, ← mul_assoc, ← Algebra.commutes s, hS]; simp only [mul_assoc]
    exact e2.trans e1.symm
  · have hbi : sh G bi = bi := by
      have h3 : sh G (β : G.C) * sh G bi = 1 := by rw [← shm, hbi_def, Units.inv_mul, sh1]
      rw [hβ] at h3
      calc sh G bi = (bi * β) * sh G bi := by rw [hbi_def, Units.inv_mul, one_mul]
        _ = bi := by rw [mul_assoc, h3, mul_one]
    simp only [shm, shs, hβ, hbi, mul_assoc, hC]

theorem grp_conj_unit_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 →
    IsUnit (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ Commute (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧
    (β : G.C) * sh G (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * ((β⁻¹ : G.Cˣ) : G.C) = (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ y y₀ c hy hs
  have h0 : (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) * β := y₀.2.1
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C ((y : G.Cˣ × ℚˣ).2 : ℚ) * β := y.2.1
  rw [hy, hs] at h1
  exact unit_conj_form_props G β _ c _ hβ h0 h1

end GlobalTheory
end

