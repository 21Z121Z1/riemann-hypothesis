import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestDataHaarFactorizationStatement

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfIsBlockEmb
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockLevel

open Matrix
open scoped TensorProduct
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance isModTopAFE : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem finiteDimensional_FE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

local instance : FiniteDimensional F E := finiteDimensional_FE

local instance topRingAFE : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_sigR_ad (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add, LinearMap.map_add, ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem infTens_sigR (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) :
    GlobalTheory.LFun.infTens F E (sigR (AF F) σ z) = sigR (Ainf F) σ (GlobalTheory.LFun.infTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem continuous_finGL (d : ℕ) : Continuous (GlobalTheory.CuspRep.finGL E d) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (GlobalTheory.CuspRep.sFin E : GlobalTheory.CuspRep.Af E → GlobalTheory.CuspRep.Ad E) :=
    (continuous_const.prodMk continuous_id :
      Continuous fun x : GlobalTheory.CuspRep.Af E => ((0, x) : InfiniteAdeleRing E × GlobalTheory.CuspRep.Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E) => 1 - GlobalTheory.CuspRep.matN d (GlobalTheory.CuspRep.sFin E) 1 + x.map (GlobalTheory.CuspRep.sFin E))

variable [IsTotallyComplex E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
  {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ} {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem continuous_of_isBlockEmb (hι : GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι) : Continuous ι := by
  obtain ⟨Φ, j, -, hΦs, -, -, hf⟩ := hι
  have hval : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom (AF F) σ J (ι g)).1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := by
    simp only [hf, cT]
    have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g.1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := Units.continuous_val
    have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((g⁻¹).1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) :=
      Units.continuous_val.comp continuous_inv
    have h3 := h1.matrix_map hΦs
    have h4 := ((h2.matrix_map hΦs).matrix_map (continuous_sigR_ad σ)).matrix_transpose
    exact (continuous_const.add ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h4.sub continuous_const)).matrix_mul continuous_const)
  have hU : Continuous fun g : GlobalTheory.CuspRep.GA E d => matHom (AF F) σ J (ι g) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have : (fun g : GlobalTheory.CuspRep.GA E d => ((matHom (AF F) σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1) =
        (fun g => ((matHom (AF F) σ J (ι g)).1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) ∘ fun g => g⁻¹ := by
      funext g; simp [map_inv]
    rw [this]
    exact hval.comp continuous_inv
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 hU

theorem infTens_symm_finGL (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E)
    (hΦ : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
    (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) (a b : Fin d) :
    GlobalTheory.LFun.infTens F E (Φ.symm ((GlobalTheory.CuspRep.finGL E d k).1 a b)) = (1 : Matrix (Fin d) (Fin d) (Ainf F ⊗[F] E)) a b := by
  have e1 : GlobalTheory.LFun.infTens F E (Φ.symm ((GlobalTheory.CuspRep.finGL E d k).1 a b)) = j.symm (((GlobalTheory.CuspRep.finGL E d k).1 a b).1) := by
    have key : ∀ x, GlobalTheory.LFun.infTens F E (Φ.symm x) = j.symm x.1 := fun x => by
      have e := congrArg Prod.fst (hΦ (Φ.symm x))
      rw [RingEquiv.apply_symm_apply] at e
      rw [e, RingEquiv.symm_apply_apply]
    exact key _
  rw [e1]
  change j.symm (((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b - GlobalTheory.CuspRep.sFin E ((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E)) a b) + GlobalTheory.CuspRep.sFin E (k.1 a b)).1) = _
  change j.symm (((1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) a b).1 - 0 + 0) = _
  rw [sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem finGL_mem_finPts (hι : GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι) (k : GL (Fin d) (GlobalTheory.CuspRep.Af E)) :
    ι (GlobalTheory.CuspRep.finGL E d k) ∈ finPts σ J := by
  obtain ⟨Φ, j, -, -, -, hΦ, hf⟩ := hι
  have hA : ∀ k : GL (Fin d) (GlobalTheory.CuspRep.Af E),
      (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E)) ((GlobalTheory.CuspRep.finGL E d k).1.map Φ.symm) = 1 := by
    intro k
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact infTens_symm_finGL Φ j hΦ k a b
  have hB : (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E))
      (cT (sigR (AF F) σ) ((GlobalTheory.CuspRep.finGL E d k)⁻¹.1.map Φ.symm)) = 1 := by
    rw [← map_inv]
    ext a b
    have e := congrArg (fun M => M b a) (hA k⁻¹)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, cT, Matrix.transpose_apply, infTens_sigR, e]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, map_zero]
  simp only [finPts, MonoidHom.mem_ker, MonoidHom.comp_apply]
  apply Units.ext
  change (RingHom.mapMatrix (GlobalTheory.LFun.infTens F E)) (matHom (AF F) σ J (ι (GlobalTheory.CuspRep.finGL E d k))).1 = 1
  have hA' : ((GlobalTheory.CuspRep.finGL E d k).1.map Φ.symm - 1).map (GlobalTheory.LFun.infTens F E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, hA, map_one, sub_self]
  have hB' : (cT (sigR (AF F) σ) ((GlobalTheory.CuspRep.finGL E d k)⁻¹.1.map Φ.symm) - 1).map (GlobalTheory.LFun.infTens F E) = 0 := by
    rw [← RingHom.mapMatrix_apply, map_sub, hB, map_one, sub_self]
  rw [hf]
  simp only [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_mul, hA', hB', Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem isOpen_rightInv_finGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        IsOpen {k : GL (Fin d) (GlobalTheory.CuspRep.Af E) | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)} := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι hι _ _ _ _ ψ hψ g₀ _
  obtain ⟨U, hUo, hU⟩ := hψ.1.level
  let H : Subgroup (GL (Fin d) (GlobalTheory.CuspRep.Af E)) :=
    { carrier := {k | ∀ g, ψ (ι (g * GlobalTheory.CuspRep.finGL E d k) * g₀) = ψ (ι g * g₀)}
      one_mem' := fun g => by simp
      mul_mem' := fun {a b} ha hb g => by
        show ψ (ι (g * GlobalTheory.CuspRep.finGL E d (a * b)) * g₀) = _
        rw [(GlobalTheory.CuspRep.finGL E d).map_mul a b, ← mul_assoc, hb (g * GlobalTheory.CuspRep.finGL E d a), ha g]
      inv_mem' := fun {a} ha g => by
        show ψ (ι (g * GlobalTheory.CuspRep.finGL E d a⁻¹) * g₀) = _
        have e : g * GlobalTheory.CuspRep.finGL E d a⁻¹ * GlobalTheory.CuspRep.finGL E d a = g := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
        rw [← ha (g * GlobalTheory.CuspRep.finGL E d a⁻¹), e] }
  let m : GL (Fin d) (GlobalTheory.CuspRep.Af E) → GAd σ J := fun k => g₀⁻¹ * ι (GlobalTheory.CuspRep.finGL E d k) * g₀
  have hm : Continuous m :=
    (continuous_const.mul ((continuous_of_isBlockEmb hι).comp (continuous_finGL d))).mul continuous_const
  have hN : (finPts σ J).Normal := MonoidHom.normal_ker _
  have hsub : m ⁻¹' (U : Set (GAd σ J)) ⊆ (H : Set (GL (Fin d) (GlobalTheory.CuspRep.Af E))) := by
    intro k hk g
    have hfin : m k ∈ finPts σ J := by
      have := hN.conj_mem _ (finGL_mem_finPts hι k) g₀⁻¹
      simpa [m] using this
    have e := hU (m k) hk hfin (ι g * g₀)
    rw [← e]
    simp only [m, map_mul, mul_assoc, mul_inv_cancel_left]
  have h1 : m ⁻¹' (U : Set (GAd σ J)) ∈ nhds (1 : GL (Fin d) (GlobalTheory.CuspRep.Af E)) := by
    refine hm.continuousAt.preimage_mem_nhds ?_
    have : m 1 = 1 := by simp [m]
    rw [this]
    exact hUo.mem_nhds U.one_mem
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset h1 hsub)

end GlobalTheory.BlockLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.GLTwo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def FrameOf {n n₁ n₂ r : ℕ} (c : E) (H : Plane E n n₁) (H₁ : Plane E n₁ n₂) (X Y : Matrix (Fin n) (Fin r) E)
    (h1 : 1 < r) : Prop :=
  (∀ k, X k ⟨0, by omega⟩ = H.x k) ∧ (∀ k, X k ⟨1, h1⟩ = (H.ι *ᵥ H₁.x) k) ∧
    (∀ k, Y k ⟨0, by omega⟩ = c⁻¹ * H.y k) ∧ ∀ k, Y k ⟨1, h1⟩ = c⁻¹ * (H.ι *ᵥ H₁.y) k

theorem IsHypPlane.skew (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (i j : Fin n₁) : σ (W₁.J j i) = -W₁.J i j := by
  rw [← h.2.2.2.2.2, GlobalTheory.LeviPlaneSection.gram_apply, GlobalTheory.LeviPlaneSection.gram_apply,
    GlobalTheory.LeviPlaneSection.form_skew hσ hsk (fun r => H.ι r i), neg_neg]

theorem IsHypPlane.decompA (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) (v : Fin n → AE F E) :
    ∃ (α β : AE F E) (z : Fin n₁ → AE F E), v = α • incV F H.x + β • incV F H.y + incM F H.ι *ᵥ z := by
  choose α β z hz using fun j : Fin n => GlobalTheory.UnipCocptForm.decomp σ W.J W₁.J H.x H.y H.ι hsk hσ h.1 h.2.1 h.2.2.1
    h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 hd (Pi.single j 1)
  have e : ∀ j : Fin n, (Pi.single j 1 : Fin n → AE F E) = inclR (F := F) (AF F) (α j) • incV F H.x +
      inclR (F := F) (AF F) (β j) • incV F H.y + incM F H.ι *ᵥ incV F (z j) := fun j => by
    rw [← GlobalTheory.UnipCocptForm.incV_mulVec]
    funext i
    have := congrArg (inclR (F := F) (AF F)) (congrFun (hz j) i)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Pi.single_apply, apply_ite, map_one,
      map_zero] at this
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, incV] using this
  refine ⟨∑ j, v j * inclR (F := F) (AF F) (α j), ∑ j, v j * inclR (F := F) (AF F) (β j), ∑ j, v j • incV F (z j), ?_⟩
  conv_lhs => rw [show v = ∑ j, v j • (Pi.single j 1 : Fin n → AE F E) from by
    funext i; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [e, smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem IsHypPlane.levi_unique (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) {t : (AE F E)ˣ}
    {h₁ : UA σ W₁.J} {m m' : UA σ W.J} (hm : IsLevi (W₁ := W₁) H t h₁ m) (hm' : IsLevi (W₁ := W₁) H t h₁ m') :
    m = m' := by
  refine Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun j => ?_))
  obtain ⟨α, β, z, e⟩ := h.decompA hσ hsk hd (Pi.single j 1)
  change mat m *ᵥ _ = mat m' *ᵥ _
  rw [e]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hm.1, hm.2.1, hm.2.2, hm'.1, hm'.2.1, hm'.2.2]

theorem IsHypPlane.exists_leviHom (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n}
    {W₁ : Spc F E n₁} (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) :
    ∃ M : UA σ W₁.J →* UA σ W.J, Continuous M ∧ (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) ∧
      ∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J := by
  obtain ⟨M, hc, hM, hr⟩ := GlobalTheory.LeviPlaneSection.leviSection W W₁ H hσ hsk h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2 hd
  refine ⟨MonoidHom.mk' M fun a b => h.levi_unique hσ hsk hd (hM _) ?_, hc, hM, hr⟩
  obtain ⟨ax, ay, aι⟩ := hM a
  obtain ⟨cx, cy, cι⟩ := hM b
  simp only [inv_one, Units.val_one, map_one, one_smul] at ax ay cx cy
  refine ⟨?_, ?_, ?_⟩
  · simp only [Units.val_one, one_smul]
    change (mat (M a) * mat (M b)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, cx, ax]
  · simp only [inv_one, Units.val_one, map_one, one_smul]
    change (mat (M a) * mat (M b)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, cy, ay]
  · change (mat (M a) * mat (M b)) * _ = _ * (mat a * mat b)
    rw [Matrix.mul_assoc, cι, ← Matrix.mul_assoc, aι, Matrix.mul_assoc]

theorem IsHypPlane.mem_unip_iff (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n}
    {W₁ : Spc F E n₁} (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0) {c : E}
    (hc : c ≠ 0) {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ (c • W.J.map σ) X Y) (h0 : 0 < r)
    (hX : ∀ k, X k ⟨0, h0⟩ = H.x k) (g : UA σ W.J) :
    g ∈ unip σ W H ↔ toGAd hσ W.J hc g ∈ GlobalTheory.StdPar.unip σ (c • W.J.map σ) X {⟨0, h0⟩} := by
  rw [GlobalTheory.StdPar.unip_singleton hW, GlobalTheory.UnipCocptForm.mem_unip_iff σ hσ W W₁.J H hsk h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2 hd c hc g]
  have e : GlobalTheory.StdPar.initCols X ⟨0, h0⟩ = Matrix.of fun i (_ : Fin 1) => H.x i := by
    ext i j
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    exact hX i
  rw [e]

theorem toGAd_mem_ratPts (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    (g : UA σ J) : toGAd hσ J hc g ∈ ratPts σ (c • J.map σ) ↔ g ∈ ratU σ J := by
  constructor
  · intro h
    obtain ⟨v, -, hv2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h)
    exact Subgroup.mem_subgroupOf.2 ⟨v, hv2⟩
  · intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 h
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩)
    have h2 := (toGAd hσ J hc g).2
    have e : (toGAd hσ J hc g).1.1 = m.1.map (inclR (F := F) (AF F)) := by
      change g.1.1 = _
      rw [← hm]; rfl
    change Formalism.UG.cT _ (toGAd hσ J hc g).1.1 * Matrix.map _ (inclR (F := F) (AF F)) * (toGAd hσ J hc g).1.1 =
      Matrix.map _ (inclR (F := F) (AF F)) at h2
    rw [e, GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul] at h2
    exact Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective h2

theorem continuous_toGAd (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) :
    Continuous (toGAd hσ J hc) ∧ Continuous (toGAd hσ J hc).symm :=
  ⟨continuous_subtype_val.subtype_mk _, continuous_subtype_val.subtype_mk _⟩

end GlobalTheory.ThK.GLTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryGLBlockEmbeddingPolynomialEntri
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.BlockForms

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem isBlockEmb_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  intro F E _ _ _ _ _ _ σ hσ n J _ r Xf Yf _ l d h ι hι
  obtain ⟨Φ, j, _, hΦs, -, -, hform⟩ := hι
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hσ.2.2.1
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsig : Continuous (sigR (AF F) σ) := by
    have hc := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine hc.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 : Continuous fun g : GlobalTheory.CuspRep.GA E d => g.1.map Φ.symm :=
    Units.continuous_val.matrix_map hΦs
  have h2 : Continuous fun g : GlobalTheory.CuspRep.GA E d => (g⁻¹).1.map Φ.symm :=
    Units.continuous_coe_inv.matrix_map hΦs
  have h3 : Continuous fun g : GlobalTheory.CuspRep.GA E d => Matrix.transpose (((g⁻¹).1.map Φ.symm).map (sigR (AF F) σ)) :=
    (h2.matrix_map hsig).matrix_transpose
  have hM : Continuous fun g : GlobalTheory.CuspRep.GA E d => (matHom _ σ J (ι g)).1 := by
    refine Continuous.congr ?_ fun g => (hform g).symm
    exact (continuous_const.add ((continuous_const.matrix_mul (h1.sub continuous_const)).matrix_mul continuous_const)).add
      ((continuous_const.matrix_mul (h3.sub continuous_const)).matrix_mul continuous_const)
  have hMi : Continuous fun g : GlobalTheory.CuspRep.GA E d => ((matHom _ σ J (ι g))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 := by
    refine (hM.comp continuous_inv).congr fun g => ?_
    simp only [Function.comp_apply, map_inv]
  exact (isEmbedding_matHom (AF F) σ J).continuous_iff.2 (Units.continuous_iff.2 ⟨hM, hMi⟩)

end GlobalTheory.BlockForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory.JSW

theorem eq_zero_of_whit_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  intro E _ _ _ a φ hφ hW
  have hc : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E a φ hφ.1
  have hcusp := GlobalTheory.T.isCuspidal_of_isCuspForm' E a φ hφ
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant (K := E) (n := a) φ.1 :=
    fun γ g => hφ.1.left γ g
  let V : Subgroup (GL (Fin a) (Af E)) :=
    { carrier := {k | finRep E a k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hV : ∃ V : OpenSubgroup (GroundTheory.Automorphic.AdelicGLn.FiniteAdelicGL E a),
      ∀ g, ∀ v ∈ V, φ.1 (g * GroundTheory.Automorphic.AutomorphicForm.finEmb E a v) = φ.1 g :=
    ⟨⟨V, hφ.1.level⟩, fun g v hv => by
      rw [GlobalTheory.FinConj.finEmb_eq_finGL]
      have : (finRep E a v φ).1 g = φ.1 g := by rw [show finRep E a v φ = φ from hv]
      exact this⟩
  apply Subtype.ext
  exact GroundTheory.Automorphic.MultiplicityOne.eq_zero_of_whittaker_eq_zero hc hl hcusp hV hW

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.SmGL.ParIndAdm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_finset_KO_cover (K : Subgroup (GL n k)) (hK : IsOpen (K : Set (GL n k))) :
    ∃ R : Finset (GL n k), ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K := by
  obtain ⟨R, hR⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n)).elim_finite_subcover
    (fun x : GL n k => (fun y => x⁻¹ * y) ⁻¹' (K : Set (GL n k)))
    (fun x => hK.preimage (by fun_prop))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [one_mem]⟩)
  refine ⟨R, fun w hw => ?_⟩
  obtain ⟨r, hr, h⟩ := Set.mem_iUnion₂.1 (hR hw)
  exact ⟨r, hr, h⟩

theorem eq_zero_of_fixed (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (K : Subgroup (GL n k))
    (R : Finset (GL n k)) (hR : ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K)
    (f : IndSp e ρ) (hf : f ∈ fixed (parInd e ρ) K) (h0 : ∀ r ∈ R, f.1.1 r = 0) : f = 0 := by
  have hfix : ∀ κ ∈ K, ∀ x, f.1.1 (x * κ) = f.1.1 x := fun κ hκ x => by
    have := congrArg (fun φ : IndSp e ρ => φ.1.1 x) (hf ⟨κ, hκ⟩)
    simpa using this
  apply Subtype.ext; apply Subtype.ext; funext x
  obtain ⟨u, l, w, hw, rfl⟩ := UnitInd.exists_iwasawa e x
  obtain ⟨r, hr, hrw⟩ := hR w hw
  let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
    mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
  have hw' : f.1.1 w = 0 := by
    have := hfix _ hrw r
    rw [mul_inv_cancel_left] at this
    rw [this, h0 r hr]
  show f.1.1 ((p : GL n k) * w) = 0
  rw [parInd_law, hw', map_zero, smul_zero]

theorem isAdmissible_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    [FiniteDimensional ℂ W] : IsAdmissible (parInd e ρ) := by
  refine ⟨isSmooth_parInd e ρ, fun K hKo _ => ?_⟩
  obtain ⟨R, hR⟩ := exists_finset_KO_cover K hKo
  let L : fixed (parInd e ρ) K →ₗ[ℂ] (R → W) :=
    { toFun := fun f r => f.1.1.1 r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L fun f g hfg => ?_
  rw [← sub_eq_zero]
  have h := eq_zero_of_fixed e ρ K R hR (f - g).1 (f - g).2 fun r hr => by
    have := congrFun hfg ⟨r, hr⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
    show f.1.1.1 r - g.1.1.1 r = 0
    rw [this, sub_self]
  exact Subtype.ext h

end GlobalTheory.SmGL.ParIndAdm

namespace GlobalTheory.ThK.MidJac

theorem isAdmissible_detInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x x' : ℕ) (α β : kˣ →* ℂˣ), GlobalTheory.PRep.IsAdmissible (GlobalTheory.ThK.MidJac.detInd x x' α β) := by
  intro k _ _ _ _ x x' α β
  exact GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _

end GlobalTheory.ThK.MidJac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem irrUnitary_trace_ne_zero_copyFinDS : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD ν hν H _ _ _ π hπ c hc hc0
  have hcomp : HasDSComp M π := GlobalTheory.T.discrete_series_spectral_side hDS hFl hHC hPC D V lam S M T U μa μf μ fa ff hTD H π hπ c hc hc0
  have hU : GlobalTheory.AutomorphicL2Unitary.IsSubrep π ⊤ := GlobalTheory.AutomorphicL2Unitary.isSubrep_top
  have hcopy := GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries D V S M H π hπ hcomp hU
  obtain ⟨hirr, hadm⟩ := GlobalTheory.T.finite_part_irreducible_admissible hFl D V S M H π hπ hcomp hU
  haveI : ν.IsHaarMeasure := hν.1
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν ff hfam _ (finPartDSSm M hU) hadm
  have hπc' := GlobalTheory.T.test_data_haar_factorization D V lam S M T U μa μf μ fa ff hTD ν hν H π hπ _ (finPartDSSm M hU) hirr hadm hcopy c' hc'
  have hcc : c' = c := hπc'.2.symm.trans hc.2
  subst hcc
  exact ⟨_, _, _, finPartDSSm M hU, hirr, hadm, hcopy, hc'⟩

end GlobalTheory
end

