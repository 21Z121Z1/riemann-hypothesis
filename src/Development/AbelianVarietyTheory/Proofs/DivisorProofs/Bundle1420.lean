import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerDecomposition
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFin

theorem prod {H₁ H₂ : Type} [Group H₁] [Group H₂] (θ₁ : H₁ →* H₁) (θ₂ : H₂ →* H₂) (K₁ : Subgroup H₁)
    (K₂ : Subgroup H₂) (δ₁ N₁ : H₁) (δ₂ N₂ : H₂) (h₁ : TwFin θ₁ K₁ δ₁ N₁) (h₂ : TwFin θ₂ K₂ δ₂ N₂) :
    TwFin (θ₁.prodMap θ₂) (K₁.prod K₂) (δ₁, δ₂) (N₁, N₂) := by
  intro E
  obtain ⟨D₁, hD₁⟩ := h₁ (E.image Prod.fst)
  obtain ⟨D₂, hD₂⟩ := h₂ (E.image Prod.snd)
  refine ⟨D₁ ×ˢ D₂, fun t ht ⟨e, he, k, hk, hte⟩ => ?_⟩
  have ht1 : t.1 * N₁ = N₁ * t.1 := congrArg Prod.fst ht
  have ht2 : t.2 * N₂ = N₂ * t.2 := congrArg Prod.snd ht
  obtain ⟨u₁, hu₁, d₁, hd₁, k₁, hk₁, e₁⟩ :=
    hD₁ t.1 ht1 ⟨e.1, Finset.mem_image_of_mem _ he, k.1, hk.1, congrArg Prod.fst hte⟩
  obtain ⟨u₂, hu₂, d₂, hd₂, k₂, hk₂, e₂⟩ :=
    hD₂ t.2 ht2 ⟨e.2, Finset.mem_image_of_mem _ he, k.2, hk.2, congrArg Prod.snd hte⟩
  refine ⟨(u₁, u₂), ?_, (d₁, d₂), Finset.mem_product.2 ⟨hd₁, hd₂⟩, (k₁, k₂), ⟨hk₁, hk₂⟩, Prod.ext e₁ e₂⟩
  exact Prod.ext hu₁ hu₂

theorem pi {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] (θ : ∀ i, H i →* H i)
    (K : ∀ i, Subgroup (H i)) (δ N : ∀ i, H i) (h : ∀ i, TwFin (θ i) (K i) (δ i) (N i)) :
    TwFin (Pi.monoidHom fun i => (θ i).comp (Pi.evalMonoidHom H i)) (Subgroup.pi Set.univ K) δ N := by
  intro E
  have h' := fun i => h i (E.image fun x => x i)
  choose D hD using h'
  refine ⟨Fintype.piFinset D, fun t ht ⟨e, he, k, hk, hte⟩ => ?_⟩
  have hi : ∀ i, ∃ u ∈ GlobalTheory.BCT.twCent (θ i) (δ i), ∃ d ∈ D i, ∃ k ∈ K i, t i = u * d * k := fun i =>
    hD i (t i) (congrFun ht i) ⟨e i, Finset.mem_image_of_mem _ he, k i, hk i (Set.mem_univ i), congrFun hte i⟩
  choose u hu d hd k' hk' e' using hi
  refine ⟨u, ?_, d, Fintype.mem_piFinset.2 hd, k', fun i _ => hk' i, funext e'⟩
  funext i
  exact hu i

theorem map_nrmG {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (δ : H) : f (nrmG θ r δ) = nrmG θ' r (f δ) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact Function.Semiconj.iterate_right hf i δ

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ → ∀ δ z : Gr G r, IsNrm G r γ δ z → ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ t : Gr G r, t * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * t → (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, t⁻¹ * δ * sigG G r t = e * k) → ∃ u ∈ GlobalTheory.BCT.twCent (sigG G r) δ, ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, t = u * d * k := by
  intro p _ G r hr γ hγ δ z hN
  have e2 : ∀ i, (nrmG (sigG G r) r δ).2 i = nrmRes p (G.Fw i) G.n r (δ.2 i) := fun i =>
    map_nrmG (sigG G r) _ ((Pi.evalMonoidHom _ i).comp (MonoidHom.snd _ _)) (fun x => rfl) r δ
  have hsep : ∀ i, (nrmRes p (G.Fw i) G.n r (δ.2 i)).val.charpoly.Separable := by
    intro i
    rw [← e2, hN]
    have h1 : ((z⁻¹ * inclG G r γ * z).2 i).val =
        ((z.2 i)⁻¹).val * (γ.2 i).val.map ((inclK p (G.Fw i) r : G.Fw i →+* KQ p (G.Fw i) r)) * (z.2 i).val := rfl
    rw [h1, Matrix.coe_units_inv, Matrix.charpoly_units_conj', Matrix.charpoly_map]
    exact (hγ i).map
  have key : TwFin (sigG G r) (KHT p G.m G.n r G.Fw) (δ.1, δ.2)
      ((nrmG (sigG G r) r δ).1, (nrmG (sigG G r) r δ).2) :=
    prod _ _ _ _ _ _ _ _ (GlobalTheory.T.twisted_finiteness_gl1_unramified p r hr _ _) (pi _ _ _ _ fun i => by
      rw [e2 i]; exact GlobalTheory.T.twisted_finiteness_separable_norm p (G.Fw i) inferInstance G.n r hr _ (hsep i))
  exact key

end GlobalTheory.TwFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MassNorm

open GlobalTheory.ClassParam (krylov)

section Core

variable {R : Type} [CommRing R] {m : ℕ}

theorem aeval_of_commute_cyclic {M N : Matrix (Fin m) (Fin m) R} (v : Fin m → R) (hv : IsUnit (krylov M v).det)
    (h : Commute N M) : ∃ p : R[X], N = aeval M p := by
  let a := (krylov M v)⁻¹ *ᵥ (N *ᵥ v)
  let p : R[X] := ∑ j : Fin m, monomial (j : ℕ) (a j)
  have hp : aeval M p *ᵥ v = N *ᵥ v := by
    have : krylov M v *ᵥ a = N *ᵥ v := by rw [mulVec_mulVec, mul_nonsing_inv _ hv, one_mulVec]
    rw [← this]
    ext i
    simp [p, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hc : Commute (aeval M p) M := by
    have := congrArg (aeval M) (mul_comm p X)
    rwa [map_mul, map_mul, aeval_X] at this
  refine ⟨p, ((isUnit_iff_isUnit_det _).2 hv).mul_right_cancel ?_⟩
  rw [GlobalTheory.Orb.mul_krylov_of_commute h, GlobalTheory.Orb.mul_krylov_of_commute hc, hp]

def psi (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  D.val * GlobalTheory.Tw.Phi m R * (c.mapMatrix x)ᵀ * (GlobalTheory.Tw.Phi m R)ᵀ * (D⁻¹).val

theorem PhiT_mul_Phi : (GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R = 1 := mul_eq_one_comm.1 (Phi_mul_transpose m R)

theorem psi_mul (c : R →+* R) (D : GL (Fin m) R) (x y : Matrix (Fin m) (Fin m) R) :
    psi c D (x * y) = psi c D y * psi c D x := by
  have h1 : (D⁻¹).val * D.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [psi, map_mul, Matrix.transpose_mul]
  calc _ = D.val * GlobalTheory.Tw.Phi m R * (c.mapMatrix y)ᵀ * ((GlobalTheory.Tw.Phi m R)ᵀ * ((D⁻¹).val * D.val) * GlobalTheory.Tw.Phi m R) *
        (c.mapMatrix x)ᵀ * (GlobalTheory.Tw.Phi m R)ᵀ * (D⁻¹).val := by
        rw [h1, Matrix.mul_one, PhiT_mul_Phi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem psi_add (c : R →+* R) (D : GL (Fin m) R) (x y : Matrix (Fin m) (Fin m) R) :
    psi c D (x + y) = psi c D x + psi c D y := by
  simp only [psi, map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem psi_smul (c : R →+* R) (D : GL (Fin m) R) (r : R) (x : Matrix (Fin m) (Fin m) R) :
    psi c D (r • x) = c r • psi c D x := by
  have : c.mapMatrix (r • x) = c r • c.mapMatrix x := by ext i j; simp
  simp only [psi, this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem psi_one (c : R →+* R) (D : GL (Fin m) R) : psi c D 1 = 1 := by
  simp only [psi, map_one, Matrix.transpose_one, Matrix.mul_one]
  rw [Matrix.mul_assoc D.val, Phi_mul_transpose, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem psi_pow (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    psi c D (x ^ k) = psi c D x ^ k := by
  induction k with
  | zero => simp [psi_one]
  | succ k ih => rw [pow_succ, psi_mul, ih, pow_succ']

theorem psi_aeval (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) (p : R[X]) :
    psi c D (aeval x p) = aeval (psi c D x) (p.map c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, psi_add, hp, hq, Polynomial.map_add, map_add]
  | monomial k r =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, psi_smul, psi_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem psi_units (c : R →+* R) (D h : GL (Fin m) R) :
    psi c D h.val = (D * thetaGL m c h⁻¹ * D⁻¹).val := by
  rw [Units.val_mul, Units.val_mul, GlobalTheory.LocTwist.thetaGL_val, inv_inv]
  simp only [psi, Matrix.mul_assoc]

theorem twCent_le (c : R →+* R) (hc : ∀ x, c (c x) = x) (D₁ D₂ : GL (Fin m) R)
    (hN : D₁ * thetaGL m c D₁ = D₂ * thetaGL m c D₂) (v : Fin m → R)
    (hv : IsUnit (krylov (D₁ * thetaGL m c D₁).val v).det) :
    twCent (thetaGL m c) D₁ ≤ twCent (thetaGL m c) D₂ := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  have hpsiN : ∀ D : GL (Fin m) R, psi c D (D * thetaGL m c D).val = ((D * thetaGL m c D)⁻¹).val := by
    intro D
    rw [psi_units]
    congr 1
    simp only [_root_.mul_inv_rev, map_mul, map_inv, hθ]
    group
  have hmem : ∀ (D g : GL (Fin m) R), g ∈ twCent (thetaGL m c) D ↔ psi c D g.val = (g⁻¹).val := by
    intro D g
    rw [psi_units]
    constructor
    · intro h
      have h' : g⁻¹ * D = D * thetaGL m c g⁻¹ := (twCent (thetaGL m c) D).inv_mem h
      congr 1
      rw [← h']; group
    · intro h
      have h' : D * thetaGL m c g⁻¹ * D⁻¹ = g⁻¹ := Units.ext h
      have : g⁻¹ ∈ twCent (thetaGL m c) D := by
        change g⁻¹ * D = D * thetaGL m c g⁻¹
        calc g⁻¹ * D = (D * thetaGL m c g⁻¹ * D⁻¹) * D := by rw [h']
          _ = _ := by group
      simpa using (twCent (thetaGL m c) D).inv_mem this
  intro g hg
  have hcomm : g * (D₁ * thetaGL m c D₁) = (D₁ * thetaGL m c D₁) * g := by
    have h1 : g * D₁ = D₁ * thetaGL m c g := hg
    have h2 : thetaGL m c g = D₁⁻¹ * g * D₁ := by rw [mul_assoc, h1]; group
    have h3 := congrArg (thetaGL m c) h2
    rw [hθ, map_mul, map_mul, map_inv, h2] at h3
    calc g * (D₁ * thetaGL m c D₁)
        = (D₁ * thetaGL m c D₁) * ((thetaGL m c D₁)⁻¹ * (D₁⁻¹ * g * D₁) * thetaGL m c D₁) := by group
      _ = _ := by rw [← h3]
  obtain ⟨p, hp⟩ := aeval_of_commute_cyclic v hv (N := g.val) (by
    change g.val * (D₁ * thetaGL m c D₁).val = (D₁ * thetaGL m c D₁).val * g.val
    rw [← Units.val_mul, ← Units.val_mul, hcomm])
  have e1 := psi_aeval c D₁ (D₁ * thetaGL m c D₁).val p
  rw [hpsiN] at e1
  have e2 := psi_aeval c D₂ (D₂ * thetaGL m c D₂).val p
  rw [hpsiN, ← hN] at e2
  rw [hmem] at hg ⊢
  rw [← hg, hp, e1, e2]

end Core

section Global

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem thF_ratF (m : ℕ) (g : GL (Fin m) E) : thF E m (ratF E m g) = ratF E m (thE E m g) :=
  (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (Af E)) _ _
    (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g).symm

theorem isClosed_twCent_thF (m : ℕ) (δ : GL (Fin m) (Af E)) : IsClosed (twCent (thF E m) δ : Set (GL (Fin m) (Af E))) := by
  have e : (twCent (thF E m) δ : Set (GL (Fin m) (Af E))) = {g | (g * δ).val = (δ * thF E m g).val} := by
    ext g; exact Units.ext_iff
  rw [e]
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  exact isClosed_eq (Units.continuous_val.comp (continuous_id.mul continuous_const))
    (Units.continuous_val.comp (continuous_const.mul (GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _))))

theorem mass_eq_of_charpoly (m : ℕ) (δ₁ δ₂ : GL (Fin m) E)
    (h : (δ₂ * thE E m δ₂).val.charpoly = (δ₁ * thE E m δ₁).val.charpoly)
    (hs : (δ₁ * thE E m δ₁).val.charpoly.Separable) :
    mass (thF E m) (ratF E m).range (ratF E m δ₂) = mass (thF E m) (ratF E m).range (ratF E m δ₁) := by
  have hθE : ∀ g, thE E m (thE E m g) = g :=
    GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x)
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (A := E) (M := (δ₁ * thE E m δ₁).val) hs h
  have hx' : (δ₂ * thE E m δ₂) * x = x * (δ₁ * thE E m δ₁) := Units.ext hx
  have hu : (x⁻¹ * δ₂ * thE E m x) * thE E m (x⁻¹ * δ₂ * thE E m x) = δ₁ * thE E m δ₁ := by
    simp only [map_mul, map_inv, hθE]
    calc _ = x⁻¹ * ((δ₂ * thE E m δ₂) * x) := by group
      _ = _ := by rw [hx']; group
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hN : ratF E m δ₁ * thF E m (ratF E m δ₁) =
      ratF E m (x⁻¹ * δ₂ * thE E m x) * thF E m (ratF E m (x⁻¹ * δ₂ * thE E m x)) := by
    rw [thF_ratF, thF_ratF, ← map_mul, ← map_mul, hu]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E m δ₁ * thF E m (ratF E m δ₁)).val (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [thF_ratF, ← map_mul]
    exact h1
  have heq : twCent (thF E m) (ratF E m δ₁) = twCent (thF E m) (ratF E m (x⁻¹ * δ₂ * thE E m x)) :=
    le_antisymm (twCent_le _ hc _ _ hN _ hv') (twCent_le _ hc _ _ hN.symm _ (hN ▸ hv'))
  set y := ratF E m x with hy
  have hconj : ratF E m (x⁻¹ * δ₂ * thE E m x) = y⁻¹ * ratF E m δ₂ * thF E m y := by
    rw [hy, thF_ratF, map_mul, map_mul, map_inv]
  have hT : twCent (thF E m) (ratF E m δ₁) = (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [heq, hconj, GlobalTheory.TwOrbConj.twCent_conj]
  have hf : ∀ t : twCent (thF E m) (ratF E m δ₂), y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ twCent (thF E m) (ratF E m δ₁) := by
    intro t
    rw [hT]
    exact ⟨t, t.2, by simp [MulAut.conj_apply]⟩
  have hg : ∀ s : twCent (thF E m) (ratF E m δ₁), y * (s : GL (Fin m) (Af E)) * y⁻¹ ∈ twCent (thF E m) (ratF E m δ₂) := by
    intro s
    have hs' : (s : GL (Fin m) (Af E)) ∈ (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom :=
      hT ▸ s.2
    obtain ⟨t, ht, he⟩ := hs'
    have : (s : GL (Fin m) (Af E)) = y⁻¹ * t * y := by rw [← he]; simp [MulAut.conj_apply]
    rw [this]; simpa [mul_assoc] using ht
  let e : twCent (thF E m) (ratF E m δ₂) ≃ₜ* twCent (thF E m) (ratF E m δ₁) :=
    { toFun := fun t => ⟨y⁻¹ * t * y, hf t⟩
      invFun := fun s => ⟨y * s * y⁻¹, hg s⟩
      left_inv := fun t => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
      continuous_invFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _ }
  have hyΓ : y ∈ (ratF E m).range := ⟨x, rfl⟩
  refine GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv _ _ (thF E m) (thF E m) _ _ (ratF E m δ₂) (ratF E m δ₁) (isClosed_twCent_thF E m _)
    (isClosed_twCent_thF E m _) e fun t => ?_
  change (t : GL (Fin m) (Af E)) ∈ (ratF E m).range ↔ y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ (ratF E m).range
  rw [Subgroup.mul_mem_cancel_right _ hyΓ, Subgroup.mul_mem_cancel_left _ ((ratF E m).range.inv_mem hyΓ)]

end Global

end GlobalTheory.MassNorm

theorem GlobalTheory.BCT.mass_eq_kap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (δ * thE E n δ).val.charpoly ∈ Ell E n → mass (thF E n) (ratF E n).range (ratF E n δ) = kap (δ * thE E n δ).val.charpoly * 2 ^ nfac (δ * thE E n δ).val.charpoly := by
  intro E _ _ _ _ n δ hP
  have hd : (δ * thE E n δ).val.charpoly.natDegree = n := hP.2.1
  have hs : (δ * thE E n δ).val.charpoly.Separable := hP.2.2.1
  generalize hPdef : (δ * thE E n δ).val.charpoly = P at hd hs ⊢
  have hcast : ∀ (k : ℕ) (_ : k = n), (∃ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P) ∧
      ∀ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P →
        mass (thF E k) (ratF E k).range (ratF E k δ') = mass (thF E n) (ratF E n).range (ratF E n δ) := by
    intro k hk
    subst hk
    exact ⟨⟨δ, hPdef⟩, fun δ' h' => GlobalTheory.MassNorm.mass_eq_of_charpoly E k δ δ' (h'.trans hPdef.symm) (hPdef ▸ hs)⟩
  obtain ⟨hex, hm⟩ := hcast _ hd
  unfold GlobalTheory.BCT.kap GlobalTheory.BCT.nfac
  rw [dif_pos hex, hm _ hex.choose_spec, div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAtStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_eq_norm_completionTensor_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → IsField (Fv F v ⊗[F] E) →
    ∀ u : Fv F v, Valued.v u = 1 →
      ∃ z : Fv F v ⊗[F] E, algebraMap (Fv F v) (Fv F v ⊗[F] E) u = z * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ z := by
  first | exact @GlobalTheory.InertUnitNorm.unit_eq_mul_conj | exact GlobalTheory.InertUnitNorm.unit_eq_mul_conj | (intros; apply GlobalTheory.InertUnitNorm.unit_eq_mul_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLatticeStableIffConjIntegralStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLattice_stable_iff_conj_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (γ : UL n w), (∀ y, ψ (B.g * y) = ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y) → ∀ q : UL n w, ((∀ y ∈ unitLat e B ψ q, B.g * y ∈ unitLat e B ψ q) ↔ q⁻¹ * γ * q ∈ KL n w) := by
  first | exact @GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff | exact GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff | (intros; apply GlobalTheory.InertUnitOrb.LatStable.unitLat_stable_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecompositionStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_place_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : UA σ J), ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
    ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  first | exact @GlobalTheory.UnitaryPlaceSplit.exists_split_at | exact GlobalTheory.UnitaryPlaceSplit.exists_split_at | (intros; apply GlobalTheory.UnitaryPlaceSplit.exists_split_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellHaarRightTranslateInvariantStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryWeylCell_haar_rightTranslate_invariant : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ p : cellU y,
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal,
        ∫⁻ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv | exact GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhdsStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_one_units_nhds : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    {x : kˣ | ValuativeRel.valuation k (x : k) = 1} ∈ 𝓝 (1 : kˣ) := by
  first | exact @GlobalTheory.units_valuation_eq_one_mem_nhds_one | exact GlobalTheory.units_valuation_eq_one_mem_nhds_one | (intros; apply GlobalTheory.units_valuation_eq_one_mem_nhds_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralTupleLatticeCountBound
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedCount
open NumberField GlobalTheory.LatCount

theorem weighted_count : ∀ (D : D7) (κ : Type) [Fintype κ] (L : ℕ), 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ s : κ → ℝ, (∀ k, 0 < s k) → ∑' η : κ → D.host.E,
      {η : κ → D.host.E | ∀ k, IsIntegral ℤ ((L : D.host.E) * η k)}.indicator
        (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k) ^ N)⁻¹)) η ≤
      ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E) := by
  intro D κ _ L hL
  classical
  obtain ⟨C₀, hC₀, hCb⟩ := exists_repr_le D
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E)
  let P := κ × ι
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨2 * Fintype.card P, (1 + 2 * C₀ * L) ^ Fintype.card P, by positivity, fun s hs => ?_⟩
  set S := {η : κ → D.host.E | ∀ k, IsIntegral ℤ ((L : D.host.E) * η k)} with hS
  rw [← tsum_subtype S]
  let b : P → ℝ := fun p => 1 / (C₀ * L * s p.1)
  have hb : ∀ p, 0 < b p := fun p => by have := hs p.1; positivity
  let kap : (κ → D.host.E) → P → ℤ := fun η p =>
    ⌊(integralBasis D.host.E).repr ((L : D.host.E) * η p.1) p.2⌋
  have hint : ∀ η ∈ S, ∀ p : P, (((kap η p : ℤ) : ℚ)) =
      (L : ℚ) * (integralBasis D.host.E).repr (η p.1) p.2 := by
    intro η hη p
    rw [← repr_nat_mul]
    exact repr_int (hη p.1) p.2
  let G : (P → ℤ) → ℝ≥0∞ := fun z => ∏ p, ENNReal.ofReal (((1 + b p * |((z p : ℤ) : ℝ)|) ^ 2)⁻¹)
  have hpt : ∀ η : S, ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ ((η : κ → D.host.E) k)‖) / s k) ^
      (2 * Fintype.card P))⁻¹) ≤ G (kap η) := by
    rintro ⟨η, hη⟩
    show ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k) ^
      (2 * Fintype.card P))⁻¹) ≤ G (kap η)
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k := ⟨_, rfl⟩
    rw [← hT]
    have hterm : ∀ k, 0 ≤ (∑ τ, ‖tauE D τ (η k)‖) / s k := fun k =>
      div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hs k).le
    have hT0 : 0 ≤ T := by rw [hT]; exact Finset.sum_nonneg fun k _ => hterm k
    have hkp : ∀ p : P, 1 + b p * |((kap η p : ℤ) : ℝ)| ≤ 1 + T := by
      rintro ⟨k, l⟩
      have e1 : |((kap η (k, l) : ℤ) : ℝ)| =
          L * |((integralBasis D.host.E).repr (η k) l : ℝ)| := by
        have := congrArg (fun q : ℚ => (q : ℝ)) (hint η hη (k, l))
        simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_natCast] at this
        rw [this, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have hsk := hs k
      have h1 : |((integralBasis D.host.E).repr (η k) l : ℝ)| ≤
          ∑ l', |((integralBasis D.host.E).repr (η k) l' : ℝ)| :=
        Finset.single_le_sum (f := fun l' => |((integralBasis D.host.E).repr (η k) l' : ℝ)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
      have h2 := hCb (η k)
      have h3 : (∑ τ, ‖tauE D τ (η k)‖) / s k ≤ T := by
        rw [hT]
        exact Finset.single_le_sum (f := fun k => (∑ τ, ‖tauE D τ (η k)‖) / s k)
          (fun k _ => hterm k) (Finset.mem_univ k)
      have e2 : b (k, l) * |((kap η (k, l) : ℤ) : ℝ)| =
          |((integralBasis D.host.E).repr (η k) l : ℝ)| / (C₀ * s k) := by
        rw [e1]; simp only [b]; field_simp
      have h4 : |((integralBasis D.host.E).repr (η k) l : ℝ)| / (C₀ * s k) ≤
          (∑ τ, ‖tauE D τ (η k)‖) / s k := by
        rw [div_le_div_iff₀ (by positivity) hsk]
        nlinarith
      linarith
    show ENNReal.ofReal (((1 + T) ^ (2 * Fintype.card P))⁻¹) ≤
      ∏ p, ENNReal.ofReal (((1 + b p * |((kap η p : ℤ) : ℝ)|) ^ 2)⁻¹)
    rw [← ENNReal.ofReal_prod_of_nonneg (fun p _ => by have := hb p; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Finset.prod_inv_distrib]
    apply inv_anti₀ (Finset.prod_pos fun p _ => by have := hb p; positivity)
    calc ∏ p, (1 + b p * |((kap η p : ℤ) : ℝ)|) ^ 2 ≤ ∏ _p : P, (1 + T) ^ 2 :=
          Finset.prod_le_prod (fun p _ => by have := hb p; positivity)
            (fun p _ => pow_le_pow_left₀ (by have := hb p; positivity) (hkp p) 2)
      _ = (1 + T) ^ (2 * Fintype.card P) := by
          rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hinj : Function.Injective (fun η : S => kap η) := by
    rintro ⟨η, hη⟩ ⟨η', hη'⟩ h
    apply Subtype.ext
    funext k
    have hL0 : (L : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
    apply mul_left_cancel₀ hL0
    apply (integralBasis D.host.E).repr.injective
    ext l
    have h1 := hint η hη (k, l)
    have h2 := hint η' hη' (k, l)
    have h3 : kap η (k, l) = kap η' (k, l) := congrFun h (k, l)
    rw [repr_nat_mul, repr_nat_mul]
    rw [← h1, ← h2, h3]
  have hcard : Fintype.card ι = Module.finrank ℚ D.host.E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  have hbnd : ∀ p : P, 1 + 2 / b p ≤ (1 + 2 * C₀ * L) * max 1 (s p.1) := by
    intro p
    have e : 2 / b p = 2 * C₀ * L * s p.1 := by simp only [b]; field_simp
    rw [e]
    have h1 : (1 : ℝ) ≤ max 1 (s p.1) := le_max_left _ _
    have h2 : s p.1 ≤ max 1 (s p.1) := le_max_right _ _
    have : 0 ≤ 2 * C₀ * L := by positivity
    nlinarith
  calc ∑' η : S, ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ ((η : κ → D.host.E) k)‖) / s k) ^
        (2 * Fintype.card P))⁻¹)
      ≤ ∑' η : S, G (kap η) := ENNReal.tsum_le_tsum hpt
    _ ≤ ∑' z, G z := ENNReal.tsum_comp_le_tsum_of_injective hinj G
    _ = ∏ p : P, ∑' z : ℤ, ENNReal.ofReal (((1 + b p * |(z : ℝ)|) ^ 2)⁻¹) :=
        GlobalTheory.HL.tsum_pi_prod_ennreal (X := fun _ : P => ℤ)
          (fun (p : P) (z : ℤ) => ENNReal.ofReal (((1 + b p * |(z : ℝ)|) ^ 2)⁻¹))
    _ ≤ ∏ p : P, ENNReal.ofReal (1 + 2 / b p) := Finset.prod_le_prod' fun p _ => tsum_int_le (hb p)
    _ = ENNReal.ofReal (∏ p : P, (1 + 2 / b p)) :=
        (ENNReal.ofReal_prod_of_nonneg (fun p _ => by have := hb p; positivity)).symm
    _ ≤ ENNReal.ofReal ((1 + 2 * C₀ * L) ^ Fintype.card P *
          ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E) := by
        apply ENNReal.ofReal_le_ofReal
        calc ∏ p : P, (1 + 2 / b p) ≤ ∏ p : P, ((1 + 2 * C₀ * L) * max 1 (s p.1)) :=
              Finset.prod_le_prod (fun p _ => by have := hb p; positivity) (fun p _ => hbnd p)
          _ = (1 + 2 * C₀ * L) ^ Fintype.card P * ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
              congr 1
              rw [Fintype.prod_prod_type]
              refine Finset.prod_congr rfl fun k _ => ?_
              show ∏ _y : ι, max 1 (s k) = _
              rw [Finset.prod_const, Finset.card_univ, hcard]

end GlobalTheory.WeightedCount
end

