import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolution
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0507
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0504
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0225
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0238
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactor
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolution
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover

variable {E : Type} [Field E] [NumberField E]

def kcSub {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : Submodule (𝓞 E) (Fin m → 𝓞 E) where
  carrier := (Kc c : Set (Fin m → 𝓞 E))
  add_mem' := fun hx hy => (Kc c).add_mem hx hy
  zero_mem' := (Kc c).zero_mem
  smul_mem' := by
    intro r y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨r * o, ?_⟩
    have h : (fun j => algebraMap (𝓞 E) E ((r • y) j)) =
        (algebraMap (𝓞 E) E r) • fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, ← ho, map_mul, smul_eq_mul]

def pair {m : ℕ} (w : Fin m → E) : (Fin m → 𝓞 E) →ₗ[𝓞 E] E where
  toFun y := ∑ j, w j * (y j : E)
  map_add' := by
    intro y z
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r y
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change w j * ((r * y j : 𝓞 E) : E) = r • (w j * (y j : E))
    rw [Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
    ring

def bMod {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : Submodule (𝓞 E) E :=
  1 ⊔ (kcSub c).map (pair w)

theorem bMod_fg {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : (bMod c w).FG := by
  refine Submodule.FG.sup ?_ (Submodule.FG.map _ (IsNoetherian.noetherian _))
  rw [Submodule.one_eq_span]
  exact Submodule.fg_span_singleton _

variable {F : Type} [Field F] [Algebra F E]

theorem sO_mem_tor (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x)
    (hsO : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E)) {m : ℕ}
    (c : Matrix (Fin m) (Fin m) E) (hc : ∀ a b, σ (c b a) = c a b) (u : Fin m → E) (a : 𝓞 E)
    (ha : ∀ y ∈ Kc c, (a : E) * ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E)) :
    sO σ a ∈ tor c u := by
  have hmem : (sO σ a) • u ∈ lam c := by
    refine GlobalTheory.T.mem_lattice_of_dual_pairing E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) _ ?_
    intro a' hL

    have hstd : ∀ j, (Pi.single j (1 : E) : Fin m → E) ∈ intVec E m := by
      intro j i
      by_cases h : i = j
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, h]⟩
    have hent : ∀ j, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = a' j := by
      intro j
      have h1 := hL _ (Submodule.mem_sup_left (hstd j) : _ ∈ lam c)
      rw [Submodule.mem_one] at h1
      obtain ⟨o, ho⟩ := h1
      exact ⟨o, by rw [ho]; simp⟩
    choose o ho using hent
    have hcol : ∀ i, ∃ p : 𝓞 E, algebraMap (𝓞 E) E p = ∑ j, a' j * c j i := by
      intro i
      have hx : c *ᵥ (Pi.single i (1 : E) : Fin m → E) ∈ lam c :=
        Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := c.mulVecLin.restrictScalars (𝓞 E)) (hstd i))
      have h1 := hL _ hx
      rw [Submodule.mem_one] at h1
      obtain ⟨p, hp⟩ := h1
      refine ⟨p, ?_⟩
      rw [hp]
      simp [dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]
    have hy : (fun j => sO σ (o j)) ∈ Kc c := by
      intro i
      obtain ⟨p, hp⟩ := hcol i
      refine ⟨sO σ p, ?_⟩
      have e1 : algebraMap (𝓞 E) E (sO σ p) = σ (algebraMap (𝓞 E) E p) := hsO p
      rw [e1, hp, map_sum]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e2 : algebraMap (𝓞 E) E (sO σ (o j)) = σ (a' j) := by
        rw [← ho j]; exact hsO (o j)
      rw [e2, map_mul, hc i j, mul_comm]
    have h2 := ha _ hy
    rw [Submodule.mem_one] at h2 ⊢
    obtain ⟨q, hq⟩ := h2
    refine ⟨sO σ q, ?_⟩
    have e1 : algebraMap (𝓞 E) E (sO σ q) = σ (algebraMap (𝓞 E) E q) := hsO q
    rw [e1, hq, map_mul, map_sum]
    simp only [dotProduct, Finset.mul_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e3 : ((sO σ (o j) : 𝓞 E) : E) = σ (a' j) := by
      rw [hsO, ← ho j]
    simp only [e3, map_mul, hinv, Algebra.smul_def]
    have e4 : algebraMap (𝓞 E) E (sO σ a) = σ (a : E) := hsO a
    rw [e4]
    ring
  rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover in

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (b : E), (∀ t ∈ tor c u, σ (t : E) * b ∈ (1 : Submodule (𝓞 E) E)) → ∃ y : Fin m → 𝓞 E, y ∈ Kc c ∧ b - ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E) := by
  intro F E _ _ _ _ _ σ hcm m c hc u b hb
  obtain ⟨hinv, -, hsO, -⟩ := GlobalTheory.T.cm_conjugation_properties F E σ hcm
  set w : Fin m → E := fun j => σ (u j) with hw
  let B : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    ⟨bMod c w, FractionalIdeal.isFractional_of_fg (bMod_fg c w)⟩
  have hB1 : (1 : E) ∈ B := by
    change (1 : E) ∈ bMod c w
    exact Submodule.mem_sup_left (Submodule.one_le.mp le_rfl)
  have hB0 : B ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hB1
    exact one_ne_zero hB1
  have hBi : B⁻¹ ≠ 0 := inv_ne_zero hB0
  have hbB : b ∈ B := by
    have hbi : b ∈ (B⁻¹)⁻¹ := by
      rw [FractionalIdeal.mem_inv_iff hBi]
      intro x hx
      rw [FractionalIdeal.mem_inv_iff hB0] at hx
      have hx1 := hx 1 hB1
      rw [mul_one, FractionalIdeal.mem_one_iff] at hx1
      obtain ⟨a, rfl⟩ := hx1
      have ht : sO σ a ∈ tor c u := by
        refine sO_mem_tor σ hinv hsO c hc u a ?_
        intro y hy
        have hyB : ∑ j, σ (u j) * (y j : E) ∈ B := by
          change _ ∈ bMod c w
          exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := pair w) (show y ∈ kcSub c from hy))
        have := hx _ hyB
        rw [FractionalIdeal.mem_one_iff] at this
        obtain ⟨q, hq⟩ := this
        rw [Submodule.mem_one]
        exact ⟨q, hq⟩
      have h := hb _ ht
      rw [hsO, hinv] at h
      rw [Submodule.mem_one] at h
      obtain ⟨q, hq⟩ := h
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨q, ?_⟩
      rw [mul_comm]
      exact hq
    rwa [inv_inv] at hbi
  have hbB' : b ∈ bMod c w := hbB
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hbB'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
  refine ⟨y, hy, ?_⟩
  have : b - ∑ j, σ (u j) * (y j : E) = p := by
    rw [← hpz]
    change p + ∑ j, σ (u j) * (y j : E) - _ = p
    ring
  rw [this]
  exact hp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRowRepFactorization
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem torusPow_mul_rowRep_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]),
  torusPow F 2 ![a, b] * (rowRep i j c)⁻¹ =
    Ad3.uni2 (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ (a - b - i)) * torusPow F 2 ![a - i, b - j] := by
  intro F _ _ _ _ a b i j c
  have h : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have e1 : (GLnLocal.uniformizer F : F) ^ (a - i) * (GLnLocal.uniformizer F : F) ^ i =
      (GLnLocal.uniformizer F : F) ^ a := by
    rw [← zpow_natCast, ← zpow_add₀ h, sub_add_cancel]
  have e2 : (GLnLocal.uniformizer F : F) ^ (b - j) * (GLnLocal.uniformizer F : F) ^ j =
      (GLnLocal.uniformizer F : F) ^ b := by
    rw [← zpow_natCast, ← zpow_add₀ h, sub_add_cancel]
  have e3 : (GLnLocal.uniformizer F : F) ^ (a - b - i) * (GLnLocal.uniformizer F : F) ^ b =
      (GLnLocal.uniformizer F : F) ^ (a - i) := by
    rw [← zpow_add₀ h]
    congr 1
    ring
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rowRep, coe_torusPow, coe_torusPow]
  simp only [Ad3.uni2]
  have d : ∀ u v : ℤ, (diagonal fun k => (GLnLocal.uniformizer F : F) ^ (![u, v] k)) =
      !![(GLnLocal.uniformizer F : F) ^ u, 0; 0, (GLnLocal.uniformizer F : F) ^ v] := by
    intro u v
    ext r s
    fin_cases r <;> fin_cases s <;> simp
  rw [d, d]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -e1
  · linear_combination (digitSum F j c * (GLnLocal.uniformizer F : F) ^ (a - b - i)) * e2 + digitSum F j c * e3
  · linear_combination -e2

end GlobalTheory.CompanionTheory.LFUDom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolutionStatement
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_swap_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (N : H) (f₁ f₂ : H → ℂ),
  IsOpen (K : Set H) → IsCompact (K : Set H) → IsOpen (L : Set H) → L ≤ K → IsHecke L f₁ → IsHecke L f₂ → Good (MonoidHom.id H) K N →
  (∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d) →
  twOrb ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (N, 1) (fun y => f₁ y.1 * f₂ y.2) =
    twOrb (MonoidHom.id H) K N (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitSwap.main | exact GlobalTheory.CompanionTheory.SplitSwap.main | (intros; apply GlobalTheory.CompanionTheory.SplitSwap.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerZpowMemIntegersIff
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem uniformizer_zpow_mem_integers_iff :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (z : ℤ), (GLnLocal.uniformizer F : F) ^ z ∈ 𝒪[F] ↔ 0 ≤ z := by
  intro F _ _ _ _ z
  constructor
  · intro h
    by_contra hz
    have hz' : 0 < -z := by omega
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hz'.le
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
      omega
    have hlt := GLnLocal.valuation_uniformizer_lt_one F
    have hpow : (GLnLocal.uniformizer F : F) ^ m ∈ 𝒪[F] :=
      Subring.pow_mem _ (GLnLocal.uniformizer F).2 m
    have hne : (GLnLocal.uniformizer F : F) ≠ 0 := by
      intro h0
      have h1 := GLnLocal.uniformizer_ne_zero F
      exact h1 h0
    have hone : (GLnLocal.uniformizer F : F) ^ z * (GLnLocal.uniformizer F : F) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hne, ← hm]
      simp
    have hv : ValuativeRel.valuation F ((GLnLocal.uniformizer F : F) ^ z) ≤ 1 := h
    have hvm : ValuativeRel.valuation F ((GLnLocal.uniformizer F : F) ^ m) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ zero_le' hlt hm0
    have h2 : ValuativeRel.valuation F
        ((GLnLocal.uniformizer F : F) ^ z * (GLnLocal.uniformizer F : F) ^ m) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hv) hvm
    rw [hone, map_one] at h2
    exact lt_irrefl _ h2
  · intro h
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [zpow_natCast]
    exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 m

end GlobalTheory.CompanionTheory.LFUDom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalInfLeviTrivial
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem mt_mul_frame {k : ℕ} (x y : GA D B) (J : Mx D B.rank k) :
    mt B (x * y) ⬝ J = mt B x ⬝ (mt B y ⬝ J) := by
  rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul]

theorem levi_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    {a : GL (Fin t) (AE D)} (e : d.nC c * d.nB b = d.emb0 g * d.levi a) : a = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.jX = mt B (d.emb0 g * d.levi a) ⬝ d.jX := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_jX, d.nC_jX, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX] at h
  apply Units.ext
  have h' : d.pX ⬝ d.jX = d.pX ⬝ (d.jX ⬝ a.1) := congrArg (fun M => d.pX ⬝ M) h
  rw [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h'
  exact h'.symm

theorem unitary_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    (e : d.nC c * d.nB b = d.emb0 g * d.levi 1) : g = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.j0 = mt B (d.emb0 g * d.levi 1) ⬝ d.j0 := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_j0, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_add, d.nC_j0,
    ← Matrix.mul_assoc, d.nC_jX] at h
  have h' : d.p0 ⬝ (d.j0 + d.jX ⬝ b) = d.p0 ⬝ (d.j0 ⬝ mt W g) := congrArg (fun M => d.p0 ⬝ M) h
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.zero_mul,
    add_zero, Matrix.one_mul] at h'
  apply GlobalTheory.MixModel.mt_injective
  rw [← h', GlobalTheory.MixModel.mt_one]

theorem radN_disj_levM : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    ∀ x, x ∈ radN d → x ∈ levM d → x = 1 := by
  intro D B W t d x hn hm
  obtain ⟨c, b, hx⟩ := (mem_radN d).1 hn
  obtain ⟨g, a, hy⟩ := (mem_levM d).1 hm
  have e : d.nC c * d.nB b = d.emb0 g * d.levi a := hx.symm.trans hy
  have ha := levi_part_eq_one d e
  subst ha
  have hg := unitary_part_eq_one d e
  subst hg
  have h1 : d.emb0 1 * d.levi 1 = 1 := by rw [map_one, map_one, mul_one]
  exact Subtype.ext (hy.trans h1)

end GlobalTheory.CompanionTheory.QKAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalStabilizerProperty
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

theorem mt_decomp_j0 (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = (d.j0 + d.jX ⬝ b) ⬝ mt W g := by
  have e : mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) =
      mt B (d.nC c) ⬝ (mt B (d.nB b) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a))) := by
    simp only [mt_mul, Matrix.mul_assoc]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.j0 = d.j0 ⬝ mt W g := by
    rw [Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  have e₂ : mt B (d.nC c) ⬝ (d.j0 + d.jX ⬝ b) = d.j0 + d.jX ⬝ b := by
    rw [Matrix.mul_add, d.nC_j0, ← Matrix.mul_assoc, d.nC_jX]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc (mt B (d.nB b)), d.nB_j0,
    ← Matrix.mul_assoc, e₂]

theorem mt_decomp_jY (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = (d.jY + d.jX ⬝ c.1) ⬝ adj (a⁻¹).1 := by
  have e : mt B (d.nC c * (d.emb0 g * d.levi a)) = mt B (d.nC c) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a)) := by
    simp only [mt_mul]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.jY = d.jY ⬝ adj (a⁻¹).1 := by
    rw [Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]
  rw [e, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc, d.nC_jY]

theorem coordB_eq_zero (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = 0) : b = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_j0, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : mt W g ⬝ mt W g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  calc b = b ⬝ mt W g ⬝ mt W g⁻¹ := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem coordC_eq_zero (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = 0) : c = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_jY, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : adj (a⁻¹).1 ⬝ adj a.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
  apply Subtype.ext
  calc c.1 = c.1 ⬝ adj (a⁻¹).1 ⬝ adj a.1 := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem pX_levM {q : GlobalTheory.RegSW.stab d} (hq : q ∈ levM d) :
    d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0 ∧ d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0 := by
  obtain ⟨g, a, h⟩ := hq
  rw [h, mt_mul]
  constructor
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding, d.pX_j0]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc (mt B (d.emb0 g)), d.wittDecomp_anisotropicEmbedding_inclY,
      ← Matrix.mul_assoc, d.pX_jY, Matrix.zero_mul]

theorem mem_levM_of_pX {q : GlobalTheory.RegSW.stab d} (h₀ : d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0)
    (hY : d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0) : q ∈ levM d := by
  obtain ⟨n, ⟨c, b, hn⟩, m, ⟨g, a, hm⟩, e⟩ := exists_radN_mul_levM d q
  have hq : (q : GA D B) = d.nC c * d.nB b * (d.emb0 g * d.levi a) := by
    rw [e, Subgroup.coe_mul, hn, hm]
  rw [hq] at h₀ hY
  have hb := coordB_eq_zero d c b g a h₀
  subst hb
  rw [d.nB_zero, mul_one] at hY
  have hc := coordC_eq_zero d c g a hY
  subst hc
  refine (mem_levM d).2 ⟨g, a, hq.trans ?_⟩
  rw [d.nC_zero, d.nB_zero, one_mul, one_mul]

theorem isClosed_levM (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) :
    IsClosed (levM d : Set (GlobalTheory.RegSW.stab d)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : Continuous fun q : GlobalTheory.RegSW.stab d => mt B (q : GA D B) :=
    (continuous_mt B).comp continuous_subtype_val
  have h₀ : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have hY : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have e : (levM d : Set (GlobalTheory.RegSW.stab d)) = {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} ∩
      {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    Set.ext fun q => ⟨fun h => pX_levM d h, fun h => mem_levM_of_pX d h.1 h.2⟩
  rw [e]
  exact h₀.inter hY

end GlobalTheory.CompanionTheory.QKAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetEigenvectorExists
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.EigTorus

theorem eigU_complete :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) →
    ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧
      ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1 :=
  eigU_of GlobalTheory.T.iwahori_unipotent_datum GlobalTheory.T.dominant_unipotent_contraction GlobalTheory.CompanionTheory.KUFactsU.kuFacts (fun G _ _ _ => GlobalTheory.T.jacquet_lemma_holds G)

end GlobalTheory.CompanionTheory.EigTorus
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVectorStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_moving_unit_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (x : Fin (M + 2) → R ⊗[F] E), IsUnit (x 0) → ∃ g : HA R σ (hypOne J), ∀ v : Fin (M + 2) → R ⊗[F] E, ((HA.mat R σ (hypOne J) g : GL (Fin (M + 2)) (R ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary | exact GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactorStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_rankin_selberg_local_factor : Ad3.Loc2 → Ad3.R.E4 := by
  first | exact @GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified | exact GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified | (intros; apply GlobalTheory.CompanionTheory.RSUnram.rankinSelberg_unramified <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewformStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_whittaker_newform : Ad3.R.U2 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | exact GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.unipotent_conj_moves_char <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBoundStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_iwasawa_growth_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (C : ℝ), (∀ x g, W' (Ad3.uni2 x * g) = (ψ x : ℂ) * W' g) → (∀ (a : Fˣ) g, W' (Ad3.dg2 a a * g) = W' g) → (∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 a 1 * κ)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 4 : ℝ)) → ∀ (t₁ t₂ b₁ b₂ : Fˣ) (x : F), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ ≤ C * (modulus ((t₁ * b₁ * (t₂ * b₂)⁻¹ : Fˣ) : F) : ℝ) ^ (1 / 4 : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa | exact GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa | (intros; apply GlobalTheory.CompanionTheory.WhittakerIwasawa.whittaker_bound_iwasawa <;> assumption)
end

