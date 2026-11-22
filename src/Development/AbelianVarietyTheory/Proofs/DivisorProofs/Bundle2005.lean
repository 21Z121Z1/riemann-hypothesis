import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteL2ABoundWords

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section
namespace GlobalTheory.ResidueEisenstein.ModMat

theorem addEquivAddHaarChar_lrCE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j m : ℕ) [LocallyCompactSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin j) (Fin m) (AF F ⊗[F] E))] (g : GL (Fin j) (AF F ⊗[F] E)) (a : GL (Fin m) (AF F ⊗[F] E)), addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE g a) = absE F E (Matrix.GeneralLinearGroup.det g) ^ m * absE F E (Matrix.GeneralLinearGroup.det a) ^ j := by
  intro F E _ _ _ _ _ σ _ j m _ _ _ _ g a
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hchar⟩ := GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE F E j m g a
  rw [hchar, GlobalTheory.SiegelCov.addEquivAddHaarChar_mulVecCE_adele]
  have hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det g ^ m * Matrix.GeneralLinearGroup.det a ^ j) := by
    ext
    simp [hdet]
  rw [hu]
  apply NNReal.eq
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.NormScaleHaar.ideleModule_norm, map_mul, map_pow, map_pow]

end GlobalTheory.ResidueEisenstein.ModMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScale
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus

noncomputable section

namespace GlobalTheory.ResidueEisenstein.ModConj.SkewSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_skewA_iff {σ : E →ₐ[F] E} {j : ℕ} {c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} :
    c ∈ skewA σ j ↔ ∀ i k, c i k + sigR (AF F) σ (c k i) = 0 := by
  rw [mem_skewA]
  constructor
  · intro h i k
    have := congrFun (congrFun h i) k
    simpa [cT] using this
  · intro h
    ext i k
    simpa [cT] using h i k

theorem cT_apply (σ : E →ₐ[F] E) {j : ℕ} (M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (i k : Fin j) :
    cT (sigR (AF F) σ) M i k = sigR (AF F) σ (M k i) := by
  simp [cT]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  rw [← GlobalTheory.ImaginaryModulus.cA_eq_sigR, ← GlobalTheory.ImaginaryModulus.cA_eq_sigR]
  exact cA_cA σ hσ z

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  rw [← GlobalTheory.ImaginaryModulus.cA_eq_sigR]
  exact GlobalTheory.ImaginaryModulus.cA_inclR σ e

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = cA σ :=
    funext fun z => (GlobalTheory.ImaginaryModulus.cA_eq_sigR σ z).symm
  rw [this]
  exact continuous_cA σ

theorem continuous_cT (σ : E →ₐ[F] E) (j : ℕ) :
    Continuous (fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => cT (sigR (AF F) σ) M) := by
  have hs := continuous_sigR σ
  exact continuous_pi fun i => continuous_pi fun k =>
    hs.comp ((continuous_apply i).comp (continuous_apply k))

def split (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (j : ℕ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) :
    (skewA σ j × skewA σ j) ≃ₜ+ Matrix (Fin j) (Fin j) (AF F ⊗[F] E) where
  toFun p := (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
  invFun M := (⟨inclR (F := F) (AF F) (2⁻¹ : E) • (M - cT (sigR (AF F) σ) M), by
      rw [mem_skewA_iff]
      intro i k
      simp only [Matrix.smul_apply, Matrix.sub_apply, cT_apply, smul_eq_mul, map_mul, map_sub, sigR_inclR,
        sigR_sigR hσ, map_inv₀ σ 2, map_ofNat σ 2]
      ring⟩,
    ⟨inclR (F := F) (AF F) (2⁻¹ : E) • inclR (F := F) (AF F) δ⁻¹ • (M + cT (sigR (AF F) σ) M), by
      rw [mem_skewA_iff]
      intro i k
      simp only [Matrix.smul_apply, Matrix.add_apply, cT_apply, smul_eq_mul, map_mul, map_add, sigR_inclR,
        sigR_sigR hσ, map_inv₀ σ 2, map_ofNat σ 2, map_inv₀ σ δ, hδ, inv_neg, map_neg]
      ring⟩)
  left_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    rw [mem_skewA_iff] at hx hy
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AF F ⊗[F] E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have hx' : ∀ i k, sigR (AF F) σ (x k i) = -x i k := fun i k => eq_neg_of_add_eq_zero_right (hx i k)
    have hy' : ∀ i k, sigR (AF F) σ (y k i) = -y i k := fun i k => eq_neg_of_add_eq_zero_right (hy i k)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext i k
      show inclR (F := F) (AF F) (2⁻¹ : E) * ((x i k + inclR (F := F) (AF F) δ * y i k) -
        sigR (AF F) σ (x k i + inclR (F := F) (AF F) δ * y k i)) = x i k
      rw [map_add, map_mul, hx', hy', sigR_inclR, hδ, map_neg]
      linear_combination x i k * hh
    · ext i k
      show inclR (F := F) (AF F) (2⁻¹ : E) * (inclR (F := F) (AF F) δ⁻¹ * ((x i k + inclR (F := F) (AF F) δ * y i k) +
        sigR (AF F) σ (x k i + inclR (F := F) (AF F) δ * y k i))) = y i k
      rw [map_add, map_mul, hx', hy', sigR_inclR, hδ, map_neg]
      linear_combination (y i k * inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹) * hh + y i k * hc
  right_inv M := by
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AF F ⊗[F] E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    ext i k
    show inclR (F := F) (AF F) (2⁻¹ : E) * (M i k - sigR (AF F) σ (M k i)) + inclR (F := F) (AF F) δ *
      (inclR (F := F) (AF F) (2⁻¹ : E) * (inclR (F := F) (AF F) δ⁻¹ * (M i k + sigR (AF F) σ (M k i)))) = M i k
    linear_combination M i k * hh + inclR (F := F) (AF F) (2⁻¹ : E) * (M i k + sigR (AF F) σ (M k i)) * hc
  map_add' p q := by
    show ((p.1 + q.1 : skewA σ j) : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + _ • ((p.2 + q.2 : skewA σ j) : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = _
    push_cast
    rw [smul_add]
    abel
  continuous_toFun := by
    show Continuous fun p : skewA σ j × skewA σ j => (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) +
      inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
    exact (continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul (inclR (F := F) (AF F) δ))
  continuous_invFun := by
    have hc := continuous_cT σ j
    have h1 : Continuous fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        inclR (F := F) (AF F) (2⁻¹ : E) • (M - cT (sigR (AF F) σ) M) :=
      (continuous_id.sub hc).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))
    have h2 : Continuous fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        inclR (F := F) (AF F) (2⁻¹ : E) • inclR (F := F) (AF F) δ⁻¹ • (M + cT (sigR (AF F) σ) M) :=
      ((continuous_id.add hc).const_smul (inclR (F := F) (AF F) δ⁻¹)).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))
    exact (h1.subtype_mk _).prodMk (h2.subtype_mk _)

theorem split_apply (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (j : ℕ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ)
    (p : skewA σ j × skewA σ j) :
    split σ hσ j δ hδ0 hδ p = (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) +
      inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := rfl

end GlobalTheory.ResidueEisenstein.ModConj.SkewSplit

namespace GlobalTheory.ResidueEisenstein.ModConj

open GlobalTheory.ResidueEisenstein.ModConj.SkewSplit in

theorem addEquivAddHaarChar_skewA_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) [LocallyCompactSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [SecondCountableTopology (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [MeasurableSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [BorelSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] (l : (AF F ⊗[F] E)ˣ) (L : GlobalTheory.ResidueEisenstein.ModConj.skewA σ j ≃ₜ+ GlobalTheory.ResidueEisenstein.ModConj.skewA σ j), (∀ s, (L s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))) → addEquivAddHaarChar L = absE F E l ^ (j * j) := by
  intro F E _ _ _ _ _ σ hcm j _ _ _ _ l L hL
  haveI : IsTotallyReal F := hcm.1
  have hσ := GlobalTheory.ImaginaryModulus.sig_sig hcm
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.ImaginaryModulus.exists_anti hcm
  obtain ⟨-, hlc, hsc, ht2⟩ := topAE F E
  haveI : LocallyCompactSpace (AF F ⊗[F] E) := hlc
  haveI : SecondCountableTopology (AF F ⊗[F] E) := hsc
  haveI : T2Space (AF F ⊗[F] E) := ht2
  haveI : LocallyCompactSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin j → Fin j → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin j → Fin j → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := ⟨rfl⟩
  haveI : T2Space (skewA σ j) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (skewA σ j × skewA σ j) := Prod.borelSpace
  set Φ := split σ hσ j δ hδ0 hδ
  set M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) ≃ₜ+ Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    (Φ.symm.trans (GlobalTheory.ModuLR.prodCE L L)).trans Φ
  set a : (AF F ⊗[F] E)ˣ := l * GlobalTheory.Doubling.conjUnit σ l
  have ha : (a : AF F ⊗[F] E) = l * sigR (AF F) σ l := rfl
  have hM : ∀ z, M z = (a : AF F ⊗[F] E) • z := by
    intro z
    obtain ⟨p, rfl⟩ := Φ.surjective z
    show Φ (GlobalTheory.ModuLR.prodCE L L (Φ.symm (Φ p))) = (a : AF F ⊗[F] E) • Φ p
    rw [ContinuousAddEquiv.symm_apply_apply, GlobalTheory.ModuLR.prodCE_apply, split_apply, split_apply, hL, hL, ha,
      smul_add, smul_comm (inclR (F := F) (AF F) δ)]
  set g : GL (Fin j) (AF F ⊗[F] E) := Units.map (Matrix.scalar (Fin j) : (AF F ⊗[F] E) →+* _).toMonoidHom a
  have hg : Matrix.GeneralLinearGroup.det g = a ^ j := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val]
    show (Matrix.scalar (Fin j) (a : AF F ⊗[F] E)).det = _
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hT : M = GlobalTheory.ModuLR.lrCE g 1 := by
    ext u i k
    rw [hM, GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.mul_one]
    show ((a : AF F ⊗[F] E) • u) i k = (Matrix.scalar (Fin j) (a : AF F ⊗[F] E) * u) i k
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have h1 : addEquivAddHaarChar M = absE F E a ^ (j * j) := by
    rw [hT, GlobalTheory.ModuLR.chi_lr F E j j g 1, hg, map_one, map_one, one_pow, mul_one, map_pow, ← pow_mul]
  have h2 : addEquivAddHaarChar M = addEquivAddHaarChar L * addEquivAddHaarChar L := by
    rw [GlobalTheory.ModuLR.addEquivAddHaarChar_transport Φ, GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE]
  have h3 : absE F E a = absE F E l * absE F E l := by
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit]
  have h4 : addEquivAddHaarChar L * addEquivAddHaarChar L = absE F E l ^ (j * j) * absE F E l ^ (j * j) := by
    rw [← h2, h1, h3, mul_pow]
  exact (mul_self_inj (by positivity) (by positivity)).1 h4

end GlobalTheory.ResidueEisenstein.ModConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzL2WordBoundExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_l2_word_bound_exists : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  first | exact @GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound | exact GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound | (intros; apply GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFinitePartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  first | exact @GlobalTheory.WeilL2Words.dS_sum_pureA | exact GlobalTheory.WeilL2Words.dS_sum_pureA | (intros; apply GlobalTheory.WeilL2Words.dS_sum_pureA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantFirstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_nonzero_constant_first : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
          ∀ (gx : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a) → GA D A'),
            (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) → ∀ T' : Tup D P'.a P'.d P'.n,
              X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g =
                Ω₁ * ∑ᶠ x, ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ *
                  X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) := by
  first | exact @GlobalTheory.BotClassSumSmall.classSum_small | exact GlobalTheory.BotClassSumSmall.classSum_small | (intros; apply GlobalTheory.BotClassSumSmall.classSum_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumVertexLevelsContainPrincipalCongruenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_vertexLevels_contain_principalCongruence : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ i : Fin (D.R.m + 1), congLev D.sp.cm (ch.G.V (.grid i D.R.m)).gram (ch.G.Λ (.grid i D.R.m)) ch.G.modul ≤ ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2) := by
  first | exact @GlobalTheory.ClassCount.levRow_congLev_le | exact GlobalTheory.ClassCount.levRow_congLev_le | (intros; apply GlobalTheory.ClassCount.levRow_congLev_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.RestCofactor

variable {F : Type} [Field F] [NumberField F]

def shiftFin (v : Pl F) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) : κ → Af F :=
  fun i => y i + (singleFin v (x₀ i) - singleFin v (evalV F v (y i)))

theorem evalV_shiftFin (v : Pl F) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) (i : κ) :
    evalV F v (shiftFin v x₀ y i) = x₀ i := by
  simp only [shiftFin, map_add, map_sub, evalV_singleFin_self]
  abel

theorem shiftFin_back (v : Pl F) {κ : Type} (x₀ : κ → Fv F v) (y : κ → Af F) :
    shiftFin v (fun i => evalV F v (y i)) (shiftFin v x₀ y) = y := by
  funext i
  rw [shiftFin, evalV_shiftFin]
  simp only [shiftFin]
  abel

theorem continuous_shiftFin (v : Pl F) {κ : Type} :
    Continuous fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2 := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  refine continuous_pi fun i => ?_
  have h2 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.2 i := (continuous_apply i).comp continuous_snd
  have h1 : Continuous fun p : (κ → Fv F v) × (κ → Af F) => p.1 i := (continuous_apply i).comp continuous_fst
  exact h2.add (((continuous_singleFin v).comp h1).sub ((continuous_singleFin v).comp (hev.comp h2)))

theorem mem_SB_shift (v : Pl F) {κ : Type} (x₀ : κ → Fv F v) {φ' : (κ → Fv F v) → ℂ}
    (hφ' : φ' ∈ SB (κ → Fv F v)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    (fun y : κ → Af F => φ' (fun i => evalV F v (y i)) * g (shiftFin v x₀ y)) ∈ SB (κ → Af F) := by
  have hev : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have hE : Continuous fun y : κ → Af F => fun i => evalV F v (y i) :=
    continuous_pi fun i => hev.comp (continuous_apply i)
  have hS : Continuous (shiftFin v x₀) :=
    (continuous_shiftFin v).comp (continuous_const.prodMk continuous_id)
  refine ⟨(hφ'.1.comp_continuous hE).mul (hg.1.comp_continuous hS), ?_⟩
  have hK : IsCompact ((fun p : (κ → Fv F v) × (κ → Af F) => shiftFin v p.1 p.2) ''
      (tsupport φ' ×ˢ tsupport g)) := (IsCompact.prod hφ'.2 hg.2).image (continuous_shiftFin v)
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  have ha : φ' (fun i => evalV F v (y i)) ≠ 0 := left_ne_zero_of_mul hne
  have hb : g (shiftFin v x₀ y) ≠ 0 := right_ne_zero_of_mul hne
  exact hy ⟨(fun i => evalV F v (y i), shiftFin v x₀ y),
    ⟨subset_tsupport _ ha, subset_tsupport _ hb⟩, shiftFin_back v x₀ y⟩

theorem rest_of_rest : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (φ φ' : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ), φ ≠ 0 → φ' ∈ SB (κ → Fv F v) →
    Rest (evFin F v) φ r → Rest (evFin F v) φ' r := by
  intro F _ _ κ _ v φ φ' r hφ hφ' hr
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hφ
  refine ⟨hr.1, ?_⟩
  let z : (κ → AF F) → κ → AF F := fun x i =>
    pairA F 0 (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2))
  have hz : ∀ x, At (evFin F v) (z x) := by
    intro x u hu
    funext i
    refine Prod.ext ?_ ?_
    · change u.1 * 0 = 0
      exact mul_zero _
    · change u.2 * (singleFin v (x₀ i) - singleFin v (evalV F v (x i).2)) = 0
      refine af_ext fun w => ?_
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw
        have : evalV F w u.2 = 0 := hu
        rw [this, zero_mul]
      · rw [map_sub, evalV_singleFin_ne hw, evalV_singleFin_ne hw, sub_zero, mul_zero]
  have h1 : ∀ x i, ((x + z x) i).1 = (x i).1 := fun x i => by
    change (x i).1 + 0 = (x i).1
    exact add_zero _
  have h2 : ∀ x i, ((x + z x) i).2 = shiftFin v x₀ (fun i => (x i).2) i := fun x i => rfl
  have hev : ∀ x i, evFin F v ((x + z x) i) = x₀ i := fun x i => by
    change evalV F v ((x + z x) i).2 = x₀ i
    rw [h2, evalV_shiftFin]
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => φ' (fun i => evFin F v (x i)) * Φ (x + z x)
      map_add' := fun Φ Ψ => funext fun x => by simp only [Pi.add_apply]; ring
      map_smul' := fun c Φ => funext fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hL : schA F κ ≤ (schA F κ).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨f, _, mem_SB_shift v x₀ hφ' hg, funext fun x => ?_⟩
    change φ' (fun i => evFin F v (x i)) * pureA F f g (x + z x) = _
    simp only [pureA, h1, h2]
    change _ = _ * (φ' (fun i => evFin F v (x i)) * _)
    ring
  have key : tens (evFin F v) φ' r = (φ x₀)⁻¹ • L (tens (evFin F v) φ r) := by
    funext x
    change φ' (fun i => evFin F v (x i)) * r x =
      (φ x₀)⁻¹ * (φ' (fun i => evFin F v (x i)) * (φ (fun i => evFin F v ((x + z x) i)) * r (x + z x)))
    have hx : φ x₀ ≠ 0 := hx₀
    simp only [hev, hr.1 x (z x) (hz x)]
    rw [mul_left_comm (φ x₀)⁻¹, ← mul_assoc (φ x₀)⁻¹, inv_mul_cancel₀ hx, one_mul]
  rw [key]
  exact Submodule.smul_mem _ _ (hL hr.2)

end GlobalTheory.RestCofactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverComparisonScalarEqOneStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverComparison_scalar_eq_one : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∀ ζ : D.host.E, ((MulAut.conj δ γ₂ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * Matrix.scalar (Fin D.R.r) ζ → Matrix.scalar (Fin D.R.r) ζ = 1 := by
  first | exact @GlobalTheory.LevScalar.scalar_eq_one_of_conj | exact GlobalTheory.LevScalar.scalar_eq_one_of_conj | (intros; apply GlobalTheory.LevScalar.scalar_eq_one_of_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandardStatement
section
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.SumSize.OppConj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_depth_pair_standard : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → PairStdK := by
  first | exact @GlobalTheory.KerConjMean.pairStdK | exact GlobalTheory.KerConjMean.pairStdK | (intros; apply GlobalTheory.KerConjMean.pairStdK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepresentationLocalityFinitePlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilRepresentation_locality_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ g : UG (cA σ) (dbl (incM F G.W.J)), At (evFin F v) (GlobalTheory.InertDbl.matD g - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), Acts (evFin F v) (omd g) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityDbl.locality | exact GlobalTheory.WeilLocalityDbl.locality | (intros; apply GlobalTheory.WeilLocalityDbl.locality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteL2ABoundWordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_l2A_bound_words : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (n : ℕ) (R : ℝ), ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ws.length = n → (∀ h ∈ ws, ‖h‖ ≤ R) →
      GlobalTheory.WeilL2Words.l2A F μ (GlobalTheory.WeilL2Words.word F ψ ws Φ) ≤ B := by
  first | exact @GlobalTheory.WeilL2Words.l2A_word_le | exact GlobalTheory.WeilL2Words.l2A_word_le | (intros; apply GlobalTheory.WeilL2Words.l2A_word_le <;> assumption)
end

