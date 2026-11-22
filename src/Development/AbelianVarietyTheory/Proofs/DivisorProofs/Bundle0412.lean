import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationEqLatticeSeries
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoEq

theorem ofReal_prod_cpow {ι : Type} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (c : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ c = ∏ i ∈ s, ((r i : ℂ) ^ c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, ofReal_mul,
      mul_cpow_ofReal_nonneg (hr j (Finset.mem_insert_self _ _)) (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

variable {F : Type} [Field F] [NumberField F]

theorem eisTerm_eq_kFac (σ : ℂ) (z : Emb F → ℂ) (a b : F) :
    eisTerm 2 σ z (a, b) = kFac F σ * ∏ τ : Emb F, phi σ ((τ a : ℂ) + (τ b : ℂ) * z τ) := by
  unfold eisTerm kFac phi
  rw [← Finset.prod_mul_distrib, norm_prod, ofReal_prod_cpow _ _ (fun _ _ => norm_nonneg _), ← Finset.prod_inv_distrib,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hn : ‖latPt z (a, b) τ‖ = (2 * Real.pi) * ‖(τ a : ℂ) + (τ b : ℂ) * z τ‖ := by
    simp only [latPt, norm_mul, norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hn, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
  simp only [latPt, mul_inv, mul_pow]
  ring

theorem split_zero (I : FractionalIdeal (𝓞 F)⁰ F) (g : F → ℂ) (h : Summable (fun ν : {ν : F // ν ∈ I} => g ν.1)) :
    ∑' ν : {ν : F // ν ∈ I}, g ν.1 = g 0 + ∑' ν : NZ I, g ν.1 := by
  classical
  have h0 : (0 : F) ∈ I := (I : Submodule (𝓞 F) F).zero_mem
  rw [h.tsum_eq_add_tsum_ite ⟨0, h0⟩]
  congr 1
  let e : NZ I → {ν : F // ν ∈ I} := fun ν => ⟨ν.1, ν.2.1⟩
  have he : Function.Injective e := fun x y hxy => Subtype.ext (congrArg Subtype.val hxy : _)
  rw [← he.tsum_eq]
  · refine tsum_congr fun ν => ?_
    have : e ν ≠ ⟨0, h0⟩ := fun h' => ν.2.2 (congrArg Subtype.val h' : _)
    simp only [this, if_false, e]
  · intro x hx
    have hx0 : x ≠ ⟨0, h0⟩ := by
      intro h'; apply hx; simp [h']
    exact ⟨⟨x.1, x.2, fun h' => hx0 (Subtype.ext h')⟩, rfl⟩

theorem prod_abs_emb [IsTotallyReal F] (b : F) : ∏ τ : Emb F, |τ b| = |((Algebra.norm ℚ b : ℚ) : ℝ)| := by
  rw [← Finset.abs_prod]
  congr 1
  apply Complex.ofReal_injective
  push_cast
  exact prod_emb b

theorem fTerm_zero [IsTotallyReal F] (hzero : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ)) (σ : ℂ) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b : F} (hb : b ≠ 0) :
    fTerm σ z b 0 = (∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))) *
      ((|((Algebra.norm ℚ b : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  unfold fTerm
  rw [← prod_abs_emb, ofReal_prod_cpow _ _ (fun _ _ => abs_nonneg _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hy : 0 < (z τ).im := hz τ
  have hτb : τ b ≠ 0 := (map_ne_zero τ).2 hb
  rw [map_zero, zero_mul, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    hzero σ _ (mul_ne_zero hτb hy.ne'), abs_mul, abs_of_pos hy, ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg _) hy.le]
  ring

theorem gFun_eq_eisSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ σ : ℂ, 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) ∧ GlobalTheory.HeckeTwo.gFun Zb 𝔞 𝔟 σ z = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 2 σ z := by
  intro F _ _ _ 𝔞 𝔟 Zb hZ σ hσ z hz
  have hS := GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two F 𝔞 𝔟 σ hσ z hz
  refine ⟨hS, ?_⟩
  have hinv : ∀ (ε : (𝓞 F)ˣ) (a b : F),
      eisTerm 2 σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = eisTerm 2 σ z (a, b) :=
    fun ε a b => eisTerm_unit even_two σ z ε a b
  obtain ⟨-, -, hBs, hsum⟩ := GlobalTheory.T.tsum_latticePair_unitQuotient_regroup F 𝔞 𝔟 (eisTerm 2 σ z) hinv hS
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  set P : ℂ := ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) with hPdef
  set K : ℂ := kFac F σ * (omegaFactor 𝔞 : ℂ) with hKdef
  have hper : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' a : {a : F // a ∈ latM 𝔞}, eisTerm 2 σ z (a.1, c.out.1) =
        K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1 := by
    intro c
    have hb : c.out.1 ≠ 0 := c.out.2.2
    obtain ⟨hfs, hP⟩ := GlobalTheory.T.heckeWeightTwo_poisson_summation_fractionalIdeal F 𝔞 σ hσ z hz c.out.1 hb
    simp_rw [eisTerm_eq_kFac]
    rw [tsum_mul_left, hP.tsum_eq, split_zero _ _ hfs, fTerm_zero GlobalTheory.T.heckePhiFourierTransform_zero_eq σ hz hb]
    ring
  have hz2 := GlobalTheory.T.hasSum_abs_norm_cpow_unitClasses_partialZeta F 𝔟 Zb hZ (1 + 2 * σ) (by simp; linarith)
  rw [show -(1 + 2 * σ) = -1 - 2 * σ by ring] at hz2
  have hX := hz2.mul_left (K * P)
  have hT : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) := by
    simpa only [hper] using hBs
  have hY : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) :=
    (hT.sub hX.summable).congr fun c => by ring
  unfold eisSum eisClass
  rw [hsum, tsum_congr hper, hX.summable.tsum_add hY, hX.tsum_eq, tsum_mul_left]
  have hA : ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ z (c.out.1, 0) = aPart 𝔞 σ :=
    tsum_congr fun c => by simp [eisTerm, latPt]
  rw [hA]
  unfold gFun bZero bOne
  rw [if_neg hσ0]
  ring

end GlobalTheory.HeckeTwoEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandQuotientEigenDet
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.HerbrandAlg

theorem kerId : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, KernelIdentity v a Fil τ := by
  intro C _ v S _ _ a ha N Fil hF τ
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • (Submodule.Quotient.mk x : (Fin N → RS a) ⧸ Fil) = 0
    rw [← Submodule.Quotient.mk_smul, hx', Submodule.Quotient.mk_zero]
  · ext x
    constructor
    · rintro ⟨hx, hk⟩
      have hx' : lin a τ • x = 0 := hx
      have hxF : x ∈ Fil := (Submodule.Quotient.mk_eq_zero Fil).1 hk
      refine ⟨⟨x, hxF⟩, ?_, rfl⟩
      show lin a τ • (⟨x, hxF⟩ : Fil) = 0
      exact Subtype.ext hx'
    · rintro ⟨⟨y, hy⟩, hy', rfl⟩
      have hy'' : lin a τ • (⟨y, hy⟩ : Fil) = 0 := hy'
      refine ⟨?_, ?_⟩
      · show lin a τ • y = 0
        exact congrArg Subtype.val hy''
      · show (Submodule.Quotient.mk y : (Fin N → RS a) ⧸ Fil) = 0
        exact (Submodule.Quotient.mk_eq_zero Fil).2 hy

theorem core : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r := by
  intro C _ v S _ _ a ha N Fil hF τ
  obtain ⟨r, hr, hR⟩ := GlobalTheory.T.relLength_filtrationInterKerCofactor_linearFactor C v S a ha N Fil hF τ
  obtain ⟨hd, hcP, hkerc, hsat, hAX, hHc, hcH, hprojX, hHX, hFX, htf, g, hg⟩ :=
    GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hF τ
  obtain ⟨fF, fX, fK, fH, -, -, -⟩ := GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hF τ
  have tfO : ∀ (c : Int0 v) (x : Fin N → Int0 v), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc h
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left hc
  have hKF : filKer a Fil τ ≤ Fil.restrictScalars (Int0 v) := inf_le_left
  have fKs : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) := by
    rw [Module.Finite.iff_fg] at fH fK ⊢
    exact fH.sup fK
  have hle : eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ ≤ preEig a Fil τ :=
    sup_le hHX (hKF.trans hFX)
  have hA : preEig a Fil τ ⊓ LinearMap.ker (mulR a N (lin a τ)) ≤
      eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ := fun x hx =>
    Submodule.mem_sup_left (LinearMap.mem_ker.1 hx.2)
  have hmapH : (eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ :=
    eq_bot_iff.2 (by rintro _ ⟨x, hx, rfl⟩; exact (Submodule.mem_bot _).2 hx)
  have e1 : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (mulR a N (lin a τ)) =
      (filKer a Fil τ).map (mulR a N (lin a τ)) := by
    rw [Submodule.map_sup, hmapH, bot_sup_eq]
  have s1 : RelLen v (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) (preEig a Fil τ) r :=
    (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hle hA fX fKs r).2 (by rw [e1, hAX]; exact hR)
  have hC : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤
      eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ := fun x hx =>
    Submodule.mem_sup_right ⟨hsat hx, LinearMap.mem_ker.2 ((hcP x).1 (LinearMap.mem_ker.1 hx.2))⟩
  have s2 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf tfO (comp a N τ) _ _ hle hC fX fKs r).1 s1
  have hK0 : (filKer a Fil τ).map (comp a N τ) = ⊥ :=
    eq_bot_iff.2 (by
      rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot _).2 ((hcP x).2 (LinearMap.mem_ker.1 hx.2)))
  have e2 : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (comp a N τ) =
      (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
    rw [Submodule.map_sup, hK0, sup_bot_eq]
  exact ⟨r, hr, e2 ▸ s2⟩

theorem herbrandDet : HerbrandDet := by
  intro C _ v S _ _ a ha N Fil hF τ
  obtain ⟨r, hr, hR⟩ := core C v S a ha N Fil hF τ
  exact ⟨GlobalTheory.T.herbrand_determinant_identity_of_relativeLength C v S a ha N Fil hF τ r hr hR, kerId C v S a ha N Fil hF τ,
    GlobalTheory.T.herbrand_lengthIdentities_of_relativeLength C v S a ha N Fil hF τ r hr hR⟩

end GlobalTheory.HerbrandAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeAtOfPrismaticDieudonneAt
section
noncomputable section

open CategoryTheory WittVector Ideal TensorProduct Coalgebra

namespace GlobalTheory.PrismHodge

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

section Torsion

variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)

variable [Fact p.Prime] [IsDomain O]

end Torsion

section Integers

variable {p : ℕ} [Fact p.Prime] {C : Type} [NormedField C] [NormedAlgebra ℚ_[p] C]
  {O : Type} [CommRing O] [Algebra O C] (H : IsIntegers O C)
include H

theorem integers_valuation [IsUltrametricDist C] :
    (NormedField.valuation (K := C)).Integers O where
  hom_inj := H.inj
  map_le_one a := by
    rw [NormedField.valuation_apply]
    exact_mod_cast (H.mem_iff _).1 ⟨a, rfl⟩
  exists_of_le_one x hx := (H.mem_iff x).2 (by
    rw [NormedField.valuation_apply] at hx
    exact_mod_cast hx)

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

omit [IsAdicComplete (span {(p : O)}) O] in
theorem isDomain_ainf : IsDomain (Ainf p O) := by
  have : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C _ O (integers_valuation H) p
  infer_instance

end Integers

section Main

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] {ε : PreTilt O p}

theorem theta_nu_ne_zero (hε : IsPrimitiveSystem ε) : fontaineTheta O p (nu ε) ≠ 0 := by
  rw [nu, map_sub, fontaineTheta_teichmuller, map_one, sub_ne_zero]
  have : Nontrivial O := ⟨p, 1, fun h => (Fact.out : ¬IsUnit (p : O)) (h ▸ isUnit_one)⟩
  exact (hε 1).ne_one (by simpa using (Fact.out : p.Prime).one_lt)

theorem mu_ne_zero (hε : IsPrimitiveSystem ε) : Sandwich.mu ε ≠ 0 := fun h =>
  theta_nu_ne_zero hε (by rw [← phiInv_mu, h, map_zero, map_zero])

variable {C : Type} [NormedField C] [NormedAlgebra ℚ_[p] C] [IsAlgClosed C] [Algebra O C]

def PrismaticDieudonneHodgeAt (hε : IsPrimitiveSystem ε) : Prop :=
  ∃ (M : PDivGroup p O → ModuleCat.{0} (Ainf p O))
    (map : ∀ G H : PDivGroup p O, (G ⟶ H) →+ (M H →ₗ[Ainf p O] M G))
    (φ : ∀ G, M G →ₛₗ[(frobenius : Ainf p O →+* Ainf p O)] M G)
    (lie : ∀ G, M G →ₛₗ[fontaineTheta O p] G.dual.Lie)
    (dR : ∀ G, M G →ₛₗ[fontaineTheta O p] G.RigExt),
    ((∀ G, Module.Free (Ainf p O) (M G) ∧ Module.Finite (Ainf p O) (M G) ∧
      Module.finrank (Ainf p O) (M G) = G.height ∧
      Function.Injective (φ G) ∧ (∀ m, ∃ n, φ G n = frobenius (xi ε) • m) ∧
      Module.Projective O G.dual.Lie ∧ Function.Surjective (lie G) ∧
      (∀ m, lie G m = 0 ↔ ∃ n, φ G m = frobenius (xi ε) • n) ∧
      Function.Surjective (dR G) ∧ (∀ m, dR G m = 0 ↔ ∃ n, m = xi ε • n) ∧
      map G G (𝟙 G) = LinearMap.id) ∧
    (∀ (G H K : PDivGroup p O) (f : G ⟶ H) (g : H ⟶ K),
      map G K (f ≫ g) = map G H f ∘ₗ map H K g) ∧
    (∀ (G H : PDivGroup p O) (f : G ⟶ H) (m : M H),
      map G H f (φ H m) = φ G (map G H f m) ∧
      lie G (map G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie H m) ∧
      dR G (map G H f m) = rigExtMap f (dR H m)) ∧
    (∀ G H : PDivGroup p O, Function.Injective (map G H) ∧
      ∀ u : M H →ₗ[Ainf p O] M G, (∀ m, u (φ H m) = φ G (u m)) → ∃ f, map G H f = u) ∧
    ∃ (l : M (PDivGroup.mu p O)) (e : M (const p O)),
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ l) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Ainf p O) _ e) ∧
      φ _ l = frobenius (xi ε) • l ∧ φ _ e = e ∧
      map _ _ (epsHom (zeta ε) hε.zeta_zero (zeta_succ_pow ε)) l = Sandwich.mu ε • e) ∧
    (∀ (G : PDivGroup p O) (m : M G), lie G m = 0 ↔ dR G m ∈ LinearMap.range G.rigOfOmega) ∧
    ∃ ι : ∀ G : PDivGroup p O, G.VecExt ≃ₗ[O] G.dual.Lie,
      (∀ (G : PDivGroup p O) (m : M G), ι G (G.rigToExt (dR G m)) = lie G m) ∧
      ∀ (G H : PDivGroup p O) (f : G ⟶ H) (x : H.VecExt),
        ι G (vecExtMap f x) = lieMap H.dual G.dual (dualHom G H f) (ι H x)

end Main

end GlobalTheory.PrismHodge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditive
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.PostFun

variable {R : Type} [CommRing R]

theorem post_eq_cpush (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) :
    HK.post R K φ n = cpush K (resMap R φ) n := rfl

def resMapIdHomotopy (F : Shv R) : Homotopy (resMap R (𝟙 F)) (𝟙 (res R F)) := by
  have H2 := (InjectiveResolution.descIdHomotopy F (injectiveResolution F)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_id] at H2
  exact H2

def resMapCompHomotopy {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) :
    Homotopy (resMap R (φ ≫ ψ)) (resMap R φ ≫ resMap R ψ) := by
  have H2 := (InjectiveResolution.descCompHomotopy φ ψ (injectiveResolution F) (injectiveResolution G)
    (injectiveResolution M)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp] at H2
  exact H2

def resMapAddHomotopy {F G : Shv R} (φ ψ : F ⟶ G) :
    Homotopy (resMap R (φ + ψ)) (resMap R φ + resMap R ψ) := by
  have H : Homotopy (InjectiveResolution.desc (φ + ψ) (injectiveResolution G) (injectiveResolution F))
      (InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F) +
        InjectiveResolution.desc ψ (injectiveResolution G) (injectiveResolution F)) := by
    apply InjectiveResolution.descHomotopy (φ + ψ)
    · simp
    · simp [Preadditive.comp_add, Preadditive.add_comp, Functor.map_add]
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_add] at H2
  exact H2

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
  rw [← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem post_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.post R K (𝟙 F) n x = x := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapIdHomotopy F), InjResCmp.cpush_id]

theorem post_comp (K : Cx R) {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) (n : ℤ) (x : HK R K F n) :
    HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x) := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapCompHomotopy φ ψ), InjResCmp.cpush_comp]
  rfl

theorem post_add (K : Cx R) {F G : Shv R} (φ ψ : F ⟶ G) (n : ℤ) :
    HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n := by
  ext x
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapAddHomotopy φ ψ), cpush_add]
  rfl

def postHom (K : Cx R) (F G : Shv R) (n : ℤ) : (F ⟶ G) →+ (HK R K F n →+ HK R K G n) :=
  AddMonoidHom.mk' (fun φ => HK.post R K φ n) (fun φ ψ => post_add K φ ψ n)

theorem post_zsmul (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (c : ℤ) (n : ℤ) (x : HK R K F n) :
    HK.post R K (c • φ) n x = c • HK.post R K φ n x := by
  have h := map_zsmul (postHom K F G n) c φ
  exact DFunLike.congr_fun h x

theorem pull_post {K L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) (x : HK R K F n) :
    HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) :=
  ZcFun.cpull_cpush f (resMap R φ) n x

theorem main : ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ), (∀ (F : Shv R) x, HK.post R K (𝟙 F) n x = x) ∧ (∀ {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) x, HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x)) ∧ (∀ {F G : Shv R} (φ ψ : F ⟶ G), HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n) ∧ (∀ {F G : Shv R} (φ : F ⟶ G) (c : ℤ) x, HK.post R K (c • φ) n x = c • HK.post R K φ n x) ∧ ∀ {L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) x, HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) := by
  intro R _ K n
  exact ⟨fun F x => post_id K F n x, fun φ ψ x => post_comp K φ ψ n x, fun φ ψ => post_add K φ ψ n,
    fun φ c x => post_zsmul K φ c n x, fun f _ _ φ x => pull_post f φ n x⟩

end GlobalTheory.EtC.PostFun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankFibre
section
open MeasureTheory Matrix Topology

namespace GlobalTheory.RankFibre

theorem X0_mul_X0_transpose (k : Type) [Field k] (a b : ℕ) :
    GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)) * (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)))ᵀ = 1 := by
  ext i j
  rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
  simp [GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]

theorem isUnit_of_rank_mul_X0 {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k)
    (h : (A * GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b))).rank = a) : IsUnit A := by
  have h1 : A.rank = Fintype.card (Fin a) := by
    refine le_antisymm (by simpa using A.rank_le_width) ?_
    simpa [h] using Matrix.rank_mul_le_left A (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)))
  have hli : LinearIndependent k A.row := by
    rw [rank_eq_finrank_span_row] at h1
    rw [linearIndependent_iff_card_eq_finrank_span, eq_comm]; exact h1
  exact Matrix.linearIndependent_rows_iff_isUnit.1 hli

theorem integrable_fibre_integrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hl, hK⟩, hrk⟩ := hΦ
  set X0 := GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)) with hX0
  have hc1 : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X0) :=
    hl.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hc2 := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hc3 : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hcont := ((hc1.mul hc2).mul hc3).continuous

  set D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X0) ≠ 0} with hD
  have hDc : IsClosed D := by
    exact (hl.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X0 from continuous_id.matrix_mul continuous_const)
  have hDsub : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X0, subset_tsupport _ hA, ?_⟩
    show A * X0 * X0ᵀ = A
    rw [Matrix.mul_assoc, hX0, X0_mul_X0_transpose, Matrix.mul_one]
  have hDcpt : IsCompact D :=
    (hK.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X0ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hDc hDsub
  have hDr : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hr : (A * X0).rank = a := by
      by_contra hne
      exact hA (hrk _ hne)
    exact ⟨(isUnit_of_rank_mul_X0 A hr).unit, rfl⟩
  have hS : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hDcpt hDr
  have hcs : HasCompactSupport fun g : GL (Fin a) k => Φ (g.val * X0) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hS fun g hg => ?_
    have : Φ (g.val * X0) = 0 := not_not.1 hg
    simp [this]
  exact hcont.integrable_of_hasCompactSupport hcs

end GlobalTheory.RankFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnected
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem irreducibleSpace_of_smooth_of_geometricallyConnected_domain :
    ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom →
      GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := by
  intro R _ _ G hs hc _
  let K := FractionRing R
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  let F : Scheme := pullback G.hom g
  have hsnd : Smooth (pullback.snd G.hom g) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback G.hom g) hs
  have hcon : ConnectedSpace F :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) g (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hirr : IrreducibleSpace F :=
    irreducibleSpace_of_smooth_field_of_connectedSpace K _ (pullback.snd G.hom g) hsnd hcon
  have hgf : Flat g := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))
  have hG : Flat G.hom := inferInstance

  have hη : genericPoint (Spec (CommRingCat.of R)) ∈ Set.range g :=
    (Flat.generalizingMap g).stableUnderGeneralization_range
      (genericPoint_specializes (g (closedPoint K))) ⟨closedPoint K, rfl⟩
  let ξ : G.left := pullback.fst G.hom g (genericPoint F)
  have hspec : ∀ z : G.left, ξ ⤳ z := by
    intro z
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap G.hom (genericPoint_specializes (G.hom z))
    have hr : z' ∈ Set.range (pullback.fst G.hom g) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact hη
    obtain ⟨w, rfl⟩ := hr
    exact ((genericPoint_specializes w).map (pullback.fst G.hom g).continuous).trans hz'
  have hcl : closure ({ξ} : Set G.left) = Set.univ :=
    Set.eq_univ_of_forall fun z => specializes_iff_mem_closure.mp (hspec z)
  rw [irreducibleSpace_def]
  have := (isIrreducible_singleton (x := ξ)).closure
  rw [hcl] at this
  exact this

end GlobalTheory
end

