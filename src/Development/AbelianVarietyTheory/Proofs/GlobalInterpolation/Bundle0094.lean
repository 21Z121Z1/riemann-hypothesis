import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0084
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0015
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.JetIdentity

open MvPolynomial

section Lin

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_add (J J' : (DVar ι a b →₀ ℕ) → K) : jetLin (J + J') = jetLin J + jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add]

omit [Fintype ι] in
theorem jetLin_smul (c : K) (J : (DVar ι a b →₀ ℕ) → K) : jetLin (c • J) = c • jetLin J := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, Pi.smul_apply, smul_monomial]

def jetOpL (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) :
    ((DVar ι a b →₀ ℕ) → K) →ₗ[K] (Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') where
  toFun J := jetOp lam lam' J n
  map_add' J J' := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_add, LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' c J := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_smul, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

theorem jetOp_sum (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) {I : Type} [Fintype I] (ξ : I → K)
    (J : I → (DVar ι a b →₀ ℕ) → K) :
    ∑ i, ξ i • jetOp lam lam' (J i) n = jetOp lam lam' (∑ i, ξ i • J i) n := by
  have := map_sum (jetOpL (K := K) lam lam' n) (fun i => ξ i • J i) Finset.univ
  simp only [map_smul] at this
  exact this.symm

omit [Fintype ι] in
theorem jetLin_congr (J J' : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K)
    (h : ∀ μ ∈ Q.support, J (μ.comapDomain Sum.inr Sum.inr_injective.injOn) =
      J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) : jetLin J Q = jetLin J' Q := by
  rw [Q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have e : (monomial μ (coeff μ Q) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
      coeff μ Q • basisMonomials _ K μ := by
    simp [coe_basisMonomials, smul_monomial]
  rw [e, map_smul, map_smul]
  simp only [jetLin, Module.Basis.constr_basis, h μ hμ]

theorem jetOp_congr (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ((∑ β : Fin b, ∑ α : Fin a, m (τ, β, α) : ℕ) : ℤ) =
      ∑ s : Fin a, ((lam τ).w s - (lam τ).detShift + (n τ : ℤ))) → J m = J' m) :
    jetOp lam lam' J n = jetOp lam lam' J' n := by
  classical
  ext1 F
  simp only [jetOp, jetMap, LinearMap.comp_apply]
  congr 1
  refine jetLin_congr J J' _ fun μ hμ => h _ fun τ => ?_
  have h1 := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ F.2)) (mem_support_iff.mp hμ)
  rw [GlobalTheory.JetDeg.weight_derW] at h1
  simp only [Finsupp.comapDomain_apply]
  rw [h1]
  push_cast
  simp [GlobalTheory.JetDeg.natW_cast, Finset.sum_add_distrib, mul_comm]

end Lin

section An

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetC_sum (cD : ι → ℂ) {I : Type} [Fintype I] (c : I → ℂ) (G : I → VCx ι a b → ℂ)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) Set.univ) (m : DVar ι a b →₀ ℕ) :
    jetC cD (fun z => ∑ i, c i * G i z) m = ∑ i, c i * jetC cD (G i) m := by
  have hc : ∀ i (k : ℕ), ContDiff ℂ k (G i) := fun i k => (hG i).contDiff
  have e : (fun z => ∑ i, c i * G i z) = fun z => ∑ i, (c i • G i) z := by
    funext z; simp
  unfold jetC derivAt0
  rw [e, iteratedFDeriv_sum (f := fun i => c i • G i) (fun i _ => (hc i _).const_smul (c i))]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hc i _).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem map_desc {K : Type} [Field K] (σ : K →+* ℂ) {z : ℂ} (h : ∃ k : K, σ k = z) : σ (desc σ z) = z := by
  rw [desc, dif_pos h]
  exact h.choose_spec

end An

end GlobalTheory.JetIdentity

open GlobalTheory.JetIdentity in

theorem GlobalTheory.jetOp_identity_of_entire : ∀ (X : Fields) (a b : ℕ) (σ : X.K →+* ℂ) (cD : X.Tau → ℂ) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) (I₁ I₂ : Type) [Fintype I₁] [Fintype I₂] (ξ₁ : I₁ → X.K) (ξ₂ : I₂ → X.K) (G₁ : I₁ → VCx X.Tau a b → ℂ) (G₂ : I₂ → VCx X.Tau a b → ℂ) (u₁ u₂ : ℂ) (r : X.K), (∀ i, AnalyticOnNhd ℂ (G₁ i) Set.univ) → (∀ i, AnalyticOnNhd ℂ (G₂ i) Set.univ) → (∀ i (m : DVar X.Tau a b →₀ ℕ), (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) → ∃ k : X.K, σ k = u₁ * jetC cD (G₁ i) m) → (∀ i (m : DVar X.Tau a b →₀ ℕ), (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) → ∃ k : X.K, σ k = u₂ * jetC cD (G₂ i) m) → (∀ z, ∑ i, σ (ξ₁ i) * (u₁ * G₁ i z) = σ r * ∑ i, σ (ξ₂ i) * (u₂ * G₂ i z)) → ∑ i, ξ₁ i • jetOp lam lam' (fun m => desc σ (u₁ * jetC cD (G₁ i) m)) n = r • ∑ i, ξ₂ i • jetOp lam lam' (fun m => desc σ (u₂ * jetC cD (G₂ i) m)) n := by
  intro X a b σ cD lam lam' n I₁ I₂ _ _ ξ₁ ξ₂ G₁ G₂ u₁ u₂ r hG₁ hG₂ hr₁ hr₂ hz
  rw [jetOp_sum, jetOp_sum]
  refine Eq.trans ?_ ((jetOpL lam lam' n).map_smul r _)
  refine jetOp_congr lam lam' n _ _ fun m hm => ?_
  apply σ.injective
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_sum]
  have h1 := jetC_sum cD (fun i => σ (ξ₁ i) * u₁) G₁ hG₁ m
  have h2 := jetC_sum cD (fun i => σ r * (σ (ξ₂ i) * u₂)) G₂ hG₂ m
  have e : (fun z => ∑ i, σ (ξ₁ i) * u₁ * G₁ i z) = fun z => ∑ i, σ r * (σ (ξ₂ i) * u₂) * G₂ i z := by
    funext z
    have := hz z
    rw [Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  rw [e, h2] at h1
  rw [Finset.mul_sum]
  simp only [fun i => map_desc σ (hr₁ i m hm), fun i => map_desc σ (hr₂ i m hm)]
  simpa only [mul_assoc] using h1.symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemHomAtGmap
section
noncomputable section

namespace GlobalTheory.KerT.Bar

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (InBox)

section Box

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap _ _ _ _).2 (by simpa using hy))
    exact (mem_localization_gmap _ _ _ _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap _ _ _ _).1 hy)
    exact (mem_localization_gmap _ _ _ _).2 (by simpa using this)

theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    g'.symm.toLinearMap ∘ₗ (c • x) ∘ₗ g.toLinearMap = c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine LinearMap.ext fun y => ?_
  exact equiv_osmul g'.symm c (x (g y))

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K} (h : InBox S cA cB N N' Ξ)
    (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have h1 : (cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) ∈ homAt S N N' := h.1 _ hx
    change (cA : 𝓞 E) • x ∈ homAt S (gmap g N) (gmap g' N')
    rw [mem_homAt_gmap, conj_osmul]
    exact h1
  · rintro x _ ⟨z, hz, rfl⟩
    have h1 := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) = _
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]
    exact h1

end Box

variable {X : Fields}

theorem framed_gmap {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) (fun P : SB => g * fr P) := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem mem_valAt_gmap (w : HeightOneSpectrum (𝓞 X.K)) {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    y ∈ valAt w lam (gmap γ.1 L) ↔ ∃ z ∈ valAt w lam L, rhoVr X.emb lam (ufGL X.E n γ) z = y := by
  unfold valAt
  rw [delAtr_gmap, Formalism.BasicNotions.SkeletonIndexLemmas.localization_map₂]
  exact Iff.rfl

theorem rho_inv_apply {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem barTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet Z.X.E (Z.R.N i) (Z.Pr.vT u) SG) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet Z.X.E (Z.R.N (i + 1)) (Z.Pr.vT u) SG') (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.Lsh, term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y = ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2))) • y') → BarTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  obtain ⟨y', hy', he⟩ := hstd (((γ, 1) : UF Z.X.E _ × GLG Z.X.E _ SG) • d) (fun P => γ.1 * fr P)
    (((γ', 1) : UF Z.X.E _ × GLG Z.X.E _ SG') • d') (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap))
    ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩ (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1)
    (inBox_gmap hbox γ.1 γ'.1) (fun x => hint _) (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by
      rw [DecoSet.smul_val, Deco.Lsh_act _ γ.2, mem_valAt_gmap]
      exact ⟨y, hy, rfl⟩)
  rw [DecoSet.smul_val, Deco.Lsh_act _ γ'.2, mem_valAt_gmap] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  refine ⟨z, hz, ?_⟩
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul] at he
  have h2 := congrArg (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ'⁻¹)) he
  rwa [rho_inv_apply, rho_inv_apply] at h2

end GlobalTheory.KerT.Bar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MonomialEqSumJet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MonoJet

open GlobalTheory.Proof.DirectionalDerivative GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets MvPowerSeries

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ}

theorem embT_injective : Function.Injective (TaylorLogMetric.embT D) := by
  intro τ τ' h
  apply D.eTau.injective
  apply (GlobalTheory.InducedType.galK_bijective D.host).1
  refine AlgEquiv.ext fun x => D.host.φ₀.injective ?_
  exact congrArg (fun f : D.host.E →+* ℂ => f x) h

theorem lamC_injOn {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) (h : TaylorLogMetric.lamC lam x = TaylorLogMetric.lamC lam y) : x = y := by
  rw [TaylorLogMetric.lamC, TaylorLogMetric.lamC, dif_pos hx, dif_pos hy] at h
  exact congrArg Subtype.val (lam.injective h)

theorem emb_mem {A : Type} [Field A] [NumberField A] (f : A →+* ℂ) (x : A) : f x ∈ TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom f.toRatAlgHom)

theorem lamC_add {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x + y) = TaylorLogMetric.lamC lam x + TaylorLogMetric.lamC lam y := by
  rw [TaylorLogMetric.lamC, TaylorLogMetric.lamC, TaylorLogMetric.lamC, dif_pos hx, dif_pos hy, dif_pos (add_mem hx hy), ← map_add]
  rfl

theorem lamC_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i, f i ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ i ∈ s, f i) = ∑ i ∈ s, TaylorLogMetric.lamC lam (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, TaylorLogMetric.lamC, dif_pos (zero_mem _)]
    exact map_zero lam
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lamC_add lam (hf a) (sum_mem fun i _ => hf i), ih]

theorem exists_single (τ : D.what₂.Tau) : ∃ (k : ℕ) (γ : Fin k → ℂ_[p]) (x : Fin k → D.host.E),
    (∑ l, γ l * TaylorLogMetric.tauEmb D lam τ (x l) = 1) ∧ ∀ τ', τ' ≠ τ → ∑ l, γ l * TaylorLogMetric.tauEmb D lam τ' (x l) = 0 := by
  classical
  choose g hg using fun τ => exists_lamHom lam (TaylorLogMetric.embT D τ)
  have hinj : Function.Injective fun τ => (g τ : D.host.E →* ℂ_[p]) := by
    intro a b h
    apply embT_injective D
    refine RingHom.ext fun x => lamC_injOn lam (emb_mem _ _) (emb_mem _ _) ?_
    rw [hg, hg]
    exact congrArg (fun f : D.host.E →* ℂ_[p] => f x) h
  have hli : LinearIndependent ℂ_[p] fun τ => (g τ : D.host.E → ℂ_[p]) :=
    (linearIndependent_monoidHom D.host.E ℂ_[p]).comp _ hinj
  have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
  have hm : (Pi.single τ 1 : D.what₂.Tau → ℂ_[p]) ∈
      Submodule.span ℂ_[p] (Set.range (flip fun τ => (g τ : D.host.E → ℂ_[p]))) := hsp ▸ Submodule.mem_top
  obtain ⟨k, γ, v, hv⟩ := Submodule.mem_span_set'.1 hm
  choose x hx using fun l => (v l).2
  have key : ∀ τ', ∑ l, γ l * TaylorLogMetric.tauEmb D lam τ' (x l) = (Pi.single τ 1 : D.what₂.Tau → ℂ_[p]) τ' := by
    intro τ'
    rw [← hv, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Pi.smul_apply, ← hx l, TaylorLogMetric.tauEmb, hg]
    rfl
  exact ⟨k, γ, x, by rw [key, Pi.single_eq_same], fun τ' h => by rw [key, Pi.single_eq_of_ne h]⟩

open Classical in

theorem exists_vecY (v : D.what₂.Tau × Fin N' × Fin N) : ∃ (k : ℕ) (γ : Fin k → ℂ_[p])
    (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), ∑ l, γ l • vecY D lam (z l) = Pi.single v 1 := by
  obtain ⟨τ, i, j⟩ := v
  obtain ⟨k, γ, x, h1, h2⟩ := exists_single D lam τ
  refine ⟨k, γ, fun l => Matrix.single i j (x l), ?_⟩
  funext ⟨τ', i', j'⟩
  obtain ⟨g, hg⟩ := exists_lamHom lam (TaylorLogMetric.embT D τ')
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecY]
  by_cases hij : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hij
    simp only [Matrix.single_apply_same]
    by_cases hτ : τ' = τ
    · subst hτ
      rw [h1, Pi.single_eq_same]
    · rw [h2 τ' hτ, Pi.single_eq_of_ne (fun h => hτ (congrArg Prod.fst h))]
  · rw [Pi.single_eq_of_ne (fun h => hij (by simp only [Prod.mk.injEq] at h; exact ⟨h.2.1.symm, h.2.2.symm⟩))]
    simp only [TaylorLogMetric.tauEmb, hg]
    simp [Matrix.single_apply_of_ne _ _ _ _ _ hij]

theorem lam_hYY (y Y : Matrix (Fin N') (Fin N) D.host.E) :
    TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D y Y : D.host.K) : D.host.E)) =
      ∑ k : D.what₂.Tau × Fin N' × Fin N, vecY D lam y k * TaylorLogMetric.lamC lam (TaylorLogMetric.embT D k.1 (D.host.conj (Y k.2.1 k.2.2))) := by
  rw [TaylorLogMetric.hYY, ← GlobalTheory.InducedType.sum_eq_trace D, lamC_sum lam _ _ fun τ => emb_mem _ _, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨g, hg⟩ := exists_lamHom lam (TaylorLogMetric.embT D τ)
  rw [hg]
  simp only [vecY, TaylorLogMetric.tauEmb, hg, map_sum, map_mul, Fintype.sum_prod_type]

theorem dirDer_sum {σ ι : Type} [Fintype σ] (s : Finset ι) (c : ι → ℂ_[p]) (w : ι → σ → ℂ_[p]) :
    dirDer (∑ l ∈ s, c l • w l) = ∑ l ∈ s, c l • dirDer (w l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dirDer_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dirDer_add, dirDer_smul, ih]

theorem dirDer_single {σ : Type} [Fintype σ] [DecidableEq σ] (v : σ) (F : MvPowerSeries σ ℂ_[p]) :
    dirDer (Pi.single v 1) F = pderiv ℂ_[p] v F := by
  rw [dirDer_apply, Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem jet_eq {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    TaylorLogMetric.jet D lam y F = constantCoeff (derList D lam (List.ofFn y) F) := by
  rw [TaylorLogMetric.jet, foldr_der]

theorem jet_snoc {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (z : Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    TaylorLogMetric.jet D lam (Fin.snoc y z : Fin (n + 1) → _) F =
      constantCoeff (derList D lam (List.ofFn y) (dirDer (vecY D lam z) F)) := by
  rw [jet_eq, List.ofFn_succ_last]
  simp [derList]

theorem exists_comb (n : ℕ) : ∀ α : TaylorLogMetric.Mono D N N', α.degree = n →
    ∃ (ι : Type) (_ : Fintype ι) (γ : ι → ℂ_[p]) (y : ι → Fin n → Matrix (Fin N') (Fin N) D.host.E),
    (∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], jetAt F α = ∑ l, γ l * TaylorLogMetric.jet D lam (y l) F) ∧
    ∀ Y : Matrix (Fin N') (Fin N) D.host.E,
      (α.prod fun v n => TaylorLogMetric.lamC lam (TaylorLogMetric.embT D v.1 (D.host.conj (Y v.2.1 v.2.2))) ^ n) =
        ∑ l, γ l * ∏ j, TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (y l j) Y : D.host.K) : D.host.E)) := by
  classical
  induction n with
  | zero =>
    intro α hn
    rw [(Finsupp.degree_eq_zero_iff α).1 hn]
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ => Fin.elim0, fun F => ?_, fun Y => ?_⟩
    · simp [jetAt_zero, TaylorLogMetric.jet]
    · simp
  | succ n ih =>
    intro α hn
    have hα : α ≠ 0 := by rintro rfl; simp at hn
    obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 hα
    have hle : Finsupp.single x 1 ≤ α := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hx)
    obtain ⟨β, rfl⟩ : ∃ β, α = β + Finsupp.single x 1 := ⟨α - Finsupp.single x 1, (tsub_add_cancel_of_le hle).symm⟩
    have hβ : β.degree = n := by
      rw [map_add, Finsupp.degree_single] at hn
      omega
    obtain ⟨ι, _, γ, y, h1, h2⟩ := ih β hβ
    obtain ⟨k, δ, z, hz⟩ := exists_vecY D lam x
    refine ⟨ι × Fin k, inferInstance, fun l => γ l.1 * δ l.2, fun l => Fin.snoc (y l.1) (z l.2), fun F => ?_, fun Y => ?_⟩
    · rw [jetAt_add_single, h1, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← dirDer_single, ← hz, dirDer_sum, jet_eq]
      simp only [jet_snoc, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, constantCoeff_smul,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
    · rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), h2, Finsupp.prod_single_index (by simp),
        pow_one, Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e : TaylorLogMetric.lamC lam (TaylorLogMetric.embT D x.1 (D.host.conj (Y x.2.1 x.2.2))) =
          ∑ m, δ m * TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (z m) Y : D.host.K) : D.host.E)) := by
        simp only [lam_hYY, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [← mul_assoc, ← Finset.sum_mul]
        have : ∀ v, ∑ m, δ m * vecY D lam (z m) v = (Pi.single x 1 : _ → ℂ_[p]) v := fun v => by
          rw [← hz, Finset.sum_apply]; rfl
        simp only [this]
        rw [Finset.sum_eq_single x]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · simp
      rw [e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      ring

theorem monomial_eq_sum_jet : ∀ (D : D7) (p N N' : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (α : TaylorLogMetric.Mono D N N'), ∃ (k : ℕ) (γ : Fin k → ℂ_[p]) (y : Fin k → Fin α.degree → Matrix (Fin N') (Fin N) D.host.E), (∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F = ∑ l, γ l * TaylorLogMetric.jet D lam (y l) F) ∧ ∀ Y : Matrix (Fin N') (Fin N) D.host.E, (α.prod fun v n => TaylorLogMetric.lamC lam (TaylorLogMetric.embT D v.1 (D.host.conj (Y v.2.1 v.2.2))) ^ n) = ∑ l, γ l * ∏ j, TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (y l j) Y : D.host.K) : D.host.E)) := by
  intro D p N N' _ lam α
  obtain ⟨ι, _, γ, y, h1, h2⟩ := exists_comb D lam _ α rfl
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, γ ∘ e, y ∘ e, fun F => ?_, fun Y => ?_⟩
  · exact (h1 F).trans (e.sum_comp _).symm
  · exact (h2 Y).trans (e.sum_comp _).symm

end GlobalTheory.MonoJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.PeriodIdealUnit

theorem not_dvd_different {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {l : ℕ} (hl : l.Prime)
    (v : Ideal (𝓞 E)) [hvp : v.IsPrime] (hv : ((l : ℕ) : 𝓞 E) ∈ v) (h2 : ((l : ℕ) : 𝓞 E) ∉ v ^ 2) :
    ¬ v ∣ differentIdeal (𝓞 K) (𝓞 E) := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) ≤ v := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : v.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hvp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  have he : v.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v hb]
    by_contra hne
    rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
    exact h2 (by simpa using hne)
  have : Algebra.IsUnramifiedAt ℤ v := Ideal.ramificationIdx_eq_one_iff.1 he
  exact not_dvd_differentIdeal_iff.2 (Algebra.IsUnramifiedAt.of_restrictScalars ℤ v)

theorem locP_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E)
    (h1 : I ≤ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (h2 : ∃ n, n ∉ P.asIdeal ∧ n • (1 : E) ∈ I) :
    localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
  le_antisymm ((ThetaMove.localization_mono P h1).trans (localization_localization₂ P _).le)
    ((ThetaMove.localization_mono P (Submodule.one_le.2 h2 : (1 : Submodule (𝓞 E) E) ≤ localization₂ P.asIdeal I)).trans (localization_localization₂ P _).le)

theorem b_ne_zero (D : D7) :
    ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
    have h3 := D.host.𝔟_spec.2
    simp [h] at h3

theorem one_mem_inv_b (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  refine (FractionalIdeal.mem_inv_iff (b_ne_zero D)).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem locP_AA_eq_one : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)), (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal) → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  intro X D s cc δ B χ cD P hp h2 hc
  let e : 𝓞 D.host.E ≃+* 𝓞 X.E := RingOfIntegers.mapRingEquiv s.iE.symm
  have he : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 X.E) X.E (e x) = s.iE.symm (algebraMap _ D.host.E x) := fun x => rfl
  have := P.isPrime
  let v : Ideal (𝓞 D.host.E) := P.asIdeal.comap (e : 𝓞 D.host.E →+* 𝓞 X.E)
  have hvp : v.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hv1 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v := by
    rw [Ideal.mem_comap, map_natCast]; exact hmem
  have hv2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∉ v ^ 2 := fun h => by
    have h3 := Ideal.le_comap_pow (e : 𝓞 D.host.E →+* 𝓞 X.E) 2 h
    rw [Ideal.mem_comap, map_natCast] at h3
    exact h2 h3
  have hnd := not_dvd_different (K := D.host.K) hp v hv1 hv2
  have hnot : ¬ D.host.𝔟 ≤ v := fun hle => hnd (by
    rw [D.host.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := SetLike.not_le_iff_exists.1 hnot
  have hN : ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun h => by
    have h3 : IsCoprime ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) := hc.cast
    obtain ⟨a, b, hab⟩ := h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hmem)))
  refine locP_eq_one P _ ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff (b_ne_zero D)).1 ht _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine ⟨e z, hzP, Submodule.mem_one.2 ⟨e (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def, he, he, ← map_mul, map_mul (algebraMap _ D.host.E), hw]
    congr 1
    have : algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) = ((c : D.host.K) : D.host.E) := rfl
    rw [this]
    ring
  · refine ⟨_, hN, Submodule.subset_span ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, 1, one_mem_inv_b D, ?_⟩⟩
    have h1 : (((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K)) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) :=
      map_natCast ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K)) _
    rw [h1, mul_one, map_natCast, Algebra.smul_def, map_natCast, mul_one]

end GlobalTheory.PeriodIdealUnit
end
end

