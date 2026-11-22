import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0169
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0358
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermTranslateByAdaptedLatticeAutomorphisms
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem mem_mL_of_coprime_smul (I : AutInst) (g c : ℕ) (hc : Nat.Coprime c g) {v : VA I} (hv : v ∈ I.Lf)
    (hcv : (c : I.E ⊗[I.F] Af I.F) • v ∈ mL I g) : v ∈ mL I g := by
  have hb : ((c : ℤ) * Nat.gcdA c g + (g : ℤ) * Nat.gcdB c g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have hR1 : ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) * (c : I.E ⊗[I.F] Af I.F) +
      ((Nat.gcdB c g : ℤ) : I.E ⊗[I.F] Af I.F) * (g : I.E ⊗[I.F] Af I.F) = 1 := by
    have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hb
    push_cast at this
    linear_combination this
  have e : v = ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) • ((c : I.E ⊗[I.F] Af I.F) • v) +
      ((Nat.gcdB c g : ℤ) : I.E ⊗[I.F] Af I.F) • ((g : I.E ⊗[I.F] Af I.F) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, hR1, one_smul]
  have hint : ∀ n : ℤ, ∀ w ∈ mL I g, ((n : I.E ⊗[I.F] Af I.F)) • w ∈ mL I g := fun n w hw =>
    (mL I g).smul_mem (⟨(n : I.E ⊗[I.F] Af I.F), intCast_mem _ n⟩ : IntAf I.F I.E) hw
  rw [e]
  exact add_mem (hint _ _ hcv) (hint _ _ (smul_mem_mL I hv))

theorem iota_symm_inv_g {D : D7} (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹)) =
      algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹) := by
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  have hG : D.host.g 0 * D.host.g 1 = X.B.g := X.g_eq.symm
  have h1 : algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹) * ((X.B.g : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) = 1 := by
    rw [← hG, ← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hG ▸ hg)), map_one]
  have ha : ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹)) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
    rw [← map_natCast ιA.symm, ← map_mul, h1, map_one]
  have hb := inv_g X.B.I X.B.g hg
  set a := ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹))
  set b := algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹)
  calc a = a * (b * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by rw [hb, mul_one]
    _ = (a * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * b := by ring
    _ = b := by rw [ha, one_mul]

theorem hA_pair_cong (I : AutInst) (g : ℕ) (H : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hH : ∀ z ∈ mL I g, H *ᵥ z ∈ mL I g) (P P' Q Q' : VA I) (hPP : P - P' ∈ mL I g) (hQQ : Q - Q' ∈ mL I g)
    (hP' : P' ∈ I.Lf) (hHQ : H *ᵥ Q ∈ I.Lf) :
    ZMod' I g (hA I P (H *ᵥ Q) - hA I P' (H *ᵥ Q')) := by
  have e : hA I P (H *ᵥ Q) - hA I P' (H *ᵥ Q') = hA I (P - P') (H *ᵥ Q) + hA I P' (H *ᵥ (Q - Q')) := by
    have e1 : hA I P (H *ᵥ Q) = hA I (P - P') (H *ᵥ Q) + hA I P' (H *ᵥ Q) := by
      rw [← hA_add_left, sub_add_cancel]
    rw [e1, Matrix.mulVec_sub, hA_sub_right]; ring
  rw [e]
  refine Z_add I g ?_ ?_
  · rw [hA_symm I (H *ᵥ Q)]
    exact Z_sig I g (mL_Qs I g hHQ hPP)
  · exact mL_Qs I g hP' (hH _ hQQ)

end GlobalTheory.St.G.ColChar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem chi_link (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (Fr : FrQ D wt)
    (hL : FrLink X u wt ιA Fr)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) :
    X.psiEf (divN X.B.I X.B.g (ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) Fr.b Fr.bd y.1.1))) = Fr.chi y.1 := by
  have hpsi : ∀ a, Fr.psi a = X.psiEf (ιA.symm a) := hL.2.2.2
  unfold AdFrame.chi
  rw [hpsi, map_mul, iota_symm_inv_g X ιA]
  rfl

end GlobalTheory.St.G.ColChar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem psiK_eq_chi : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ hk : h ∈ Ku X u hK, ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = Fr.chi y.1 := by
  intro D X u wt ιA hW hI hK Fr hL h y hRep hk
  obtain ⟨hlat, hform, -, -, -, hrep⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  have hpsi : ∀ a, Fr.psi a = X.psiEf (ιA.symm a) := hL.2.2.2
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, -, hbb⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hz0 : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have hbw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).1
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  obtain ⟨κ, hκdef⟩ : ∃ κ : X.B.I.Gf, κ = (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u := ⟨_, rfl⟩
  have hκ : κ ∈ X.K2 := by rw [hκdef]; exact hk
  have hκK : κ ∈ X.B.I.Kset := hκ.1
  have hxK : X.xu u ∈ X.B.I.Kset := X.xu_K u
  have hxκ : X.xu u * κ = (h : X.B.I.Gf) * X.xu u := by rw [hκdef]; group
  have hhK : (h : X.B.I.Gf) ∈ X.B.I.Kset := by
    have e : (h : X.B.I.Gf) = X.xu u * κ * (X.xu u)⁻¹ := by rw [hκdef]; group
    rw [e]; exact K_mul _ (K_mul _ hxK hκK) (K_inv _ hxK)

  have hpres : ∀ x : X.B.I.Gf, x ∈ X.B.I.Kset → ∀ z ∈ mL X.B.I X.B.g, X.B.I.fmat x *ᵥ z ∈ mL X.B.I X.B.g :=
    fun x hx z hz => pres X.B.I hx X.B.g ∅ (mL X.B.I X.B.g) (by simp) (by simp) le_rfl z (mL_Mo X.B.I hz)
  have hpres1 : ∀ z ∈ mL X.B.I X.B.g, (X.B.I.fmat κ - 1) *ᵥ z ∈ mL X.B.I X.B.g :=
    fun z hz => pres1 X.B.I hκK X.B.g ∅ (mL X.B.I X.B.g) (by simp) le_rfl z (mL_Mo X.B.I hz)

  have hxinv : ∀ v : VA X.B.I, X.B.I.fmat (X.xu u) *ᵥ v = v → X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = v := by
    intro v hv
    calc X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = X.B.I.fmat (X.xu u)⁻¹ *ᵥ (X.B.I.fmat (X.xu u) *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]
  have hfixE : ∀ b, X.B.I.fmat κ *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := by
    intro b
    have h1 : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := (X.xu_fix u b).1
    have h2 := Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u h _ (Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u b)
    rw [hκdef, fmat_mul, fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, hxinv _ h1]
  have hfixZ : X.B.I.fmat κ *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) := by
    have h2 := Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u h _ (Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u)
    have hxx : X.B.I.fmat (X.xu u) *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = incl X.B.I (X.zR u) := by
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul_inv, Matrix.one_mulVec]
    rw [hκdef, fmat_mul, fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxx, h2]

  have key : ∀ v w : VA X.B.I, v ∈ X.B.I.Lf → X.B.I.fmat κ *ᵥ w = w →
      InAt X.B.I X.B.g X.B.g (v - w) → (X.B.I.fmat κ - 1) *ᵥ v ∈ mL X.B.I X.B.g := by
    intro v w hv hw hvw
    obtain ⟨c, hc, hcv⟩ := hvw
    refine mem_mL_of_coprime_smul X.B.I X.B.g c hc (K_sub_mv X.B.I hκK hv) ?_
    have hw0 : (X.B.I.fmat κ - 1) *ᵥ w = 0 := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_self]
    have e : (X.B.I.fmat κ - 1) *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (v - w)) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat κ - 1) *ᵥ v) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hw0, sub_zero]
    rw [← e]; exact hpres1 _ hcv
  have hnxt : ∀ a, (X.B.I.fmat κ - 1) *ᵥ nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g := by
    intro a
    unfold nxt
    split_ifs with ha
    · exact key _ _ (he0 _) (hfixE _) (X.basisApprox _).1
    · refine key _ _ hz0 hfixZ ?_
      obtain ⟨c, hc, hcv⟩ := X.xu_z u
      refine ⟨c, hc, ?_⟩
      have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) =
          -((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0)) := by
        rw [← smul_neg, neg_sub]
      rw [e]; exact neg_mem hcv

  have hterm : ∀ (i : Fin D.R.k) (hi : i.1 + 1 < D.R.k),
      ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, hi⟩) -
        ιA.symm (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
          (Fr.bd i) (y.1.1 *ᵥ Fr.b ⟨i.1 + 1, hi⟩))) := by
    intro i hi
    generalize hj : (⟨i.1 + 1, hi⟩ : Fin D.R.k) = j
    have hT : ιA.symm (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
          (Fr.bd i) (y.1.1 *ᵥ Fr.b j)) =
        hA X.B.I (embA X wt ιA (Fr.bd i)) (X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA (Fr.b j)) := by
      rw [← hform, RingEquiv.symm_apply_apply, hrep h y hRep]
    have hT2 : hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw j) =
        hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)
          (X.B.I.fmat (h : X.B.I.Gf) *ᵥ (X.B.I.fmat (X.xu u) *ᵥ X.bw j)) := by
      rw [← Formalism.L2.SG.PoincareInHH.Cut.hA_fmat X (X.xu u) (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw j),
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← fmat_mul, ← fmat_mul, hxκ]
    rw [hT, hT2]
    refine hA_pair_cong X.B.I X.B.g _ (hpres _ hhK) _ _ _ _ ?_ ?_ ((hlat (Fr.bd i)).1 (Fr.bd_mem i))
      (K_mv X.B.I hhK (K_mv X.B.I hxK (hbw j)))
    · have := neg_mem (hL.2.2.1 i); rwa [neg_sub] at this
    · have := neg_mem (hL.2.1 j); rwa [neg_sub] at this

  have hZ : ZMod' X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ -
      ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
        Fr.b Fr.bd y.1.1) - 0) := by
    have e : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ -
        ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
          Fr.b Fr.bd y.1.1) - 0 =
        (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a)) +
        ∑ i : Fin D.R.k, ((if hi : i.1 + 1 < D.R.k then
            hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, hi⟩) else 0) -
          ιA.symm (if hi : i.1 + 1 < D.R.k then
            hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
              (Fr.bd i) (y.1.1 *ᵥ Fr.b ⟨i.1 + 1, hi⟩) else 0)) := by
      simp only [Afun, supSum, map_sum, Finset.sum_sub_distrib]; ring
    rw [e]
    refine Z_add X.B.I X.B.g (Z_sum X.B.I X.B.g _ _ fun a _ => ?_) (Z_sum X.B.I X.B.g _ _ fun i _ => ?_)
    · exact congruence_fixed_term X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 hfe hfz a)
        (mL_Qs X.B.I X.B.g (hf0 a) (hnxt a))
    · by_cases hi : i.1 + 1 < D.R.k
      · simp only [dif_pos hi]; exact hterm i hi
      · simp only [dif_neg hi, map_zero, sub_self]; exact Z_zero X.B.I X.B.g
  have h0 : X.psiEf (divN X.B.I X.B.g 0) = 1 := by
    rw [divN, mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  calc ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ)
      = X.psiEf (divN X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ)) := by rw [hκdef]; rfl
    _ = X.psiEf (divN X.B.I X.B.g (ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D)
          (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) Fr.b Fr.bd y.1.1))) := by
      have hE := psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hZ
      rw [h0, mul_one] at hE
      exact hE
    _ = Fr.chi y.1 := by
      exact chi_link D X u wt ιA Fr hL y

end GlobalTheory.St.G.ColChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfConvolutionFixedModerateGrowth
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CuspFixed

theorem isHaarSub_map_emb {H G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (N : Subgroup H)
    (hN : IsClosed (N : Set H)) (ν : Measure H) (hν : IsHaarSub (N : Set H) ν) :
    IsClosed ((N.map ι : Subgroup G) : Set G) ∧ IsHaarSub ((N.map ι : Subgroup G) : Set G) (ν.map ι) := by
  have hme : MeasurableEmbedding ι := hι.measurableEmbedding
  have hS : ((N.map ι : Subgroup G) : Set G) = ι '' (N : Set H) := Subgroup.coe_map ι N
  obtain ⟨hne, hfc, hnull, hinv⟩ := hν
  refine ⟨by rw [hS]; exact hι.isClosedMap _ hN, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hne
    rwa [Measure.map_eq_zero_iff hme.measurable.aemeasurable] at h0
  · refine ⟨fun K hK => ?_⟩
    rw [hme.map_apply]
    exact hfc.lt_top_of_isCompact (hι.isCompact_preimage hK)
  · rw [hme.map_apply, Set.preimage_compl, hS, Set.preimage_image_eq _ hι.injective]
    exact hnull
  · intro m hm
    rw [hS] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    have hcomm : (fun z : G => ι k * z) ∘ ι = ι ∘ (fun z : H => k * z) := by
      funext z
      simp only [Function.comp_apply, map_mul]
    rw [Measure.map_map (continuous_mul_left (ι k)).measurable hme.measurable, hcomm,
      ← Measure.map_map hme.measurable (continuous_mul_left k).measurable, hinv k hk]

theorem constTerm_repro {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant] [IsFiniteMeasure ν] (f φ : G → ℂ) (hf : Continuous f) (hφ : Measurable φ) (x : G)
    (Φ : G → ℝ) (hΦ : Integrable Φ μ) (hb : ∀ᵐ m ∂ν, ∀ g, ‖φ g * f (m * x * g)‖ ≤ Φ g)
    (hr : ∀ z, f z = ∫ g, φ g * f (z * g) ∂μ) :
    Integrable (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) μ ∧
      ∫ m, f (m * x) ∂ν = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ := by
  have hmeas : Measurable (Function.uncurry fun (m g : G) => φ g * f (m * x * g)) := by
    apply Measurable.mul
    · exact hφ.comp measurable_snd
    · exact (hf.comp (by fun_prop : Continuous fun p : G × G => p.1 * x * p.2)).measurable
  have hint : Integrable (Function.uncurry fun (m g : G) => φ g * f (m * x * g)) (ν.prod μ) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hΦ) hmeas.aestronglyMeasurable ?_
    have hae := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae hb
    filter_upwards [hae] with p hp
    simpa [Function.uncurry] using hp p.2
  have hH : (fun g => ∫ m, φ g * f (m * x * g) ∂ν) =
      fun g => (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) (x * g) := by
    funext g
    beta_reduce
    rw [integral_const_mul, inv_mul_cancel_left, mul_comm]
    simp_rw [mul_assoc]
  have hI : Integrable (fun g => ∫ m, φ g * f (m * x * g) ∂ν) μ := hint.integral_prod_right
  rw [hH] at hI
  have hI2 := hI.comp_mul_left x⁻¹
  simp only [mul_inv_cancel_left] at hI2
  refine ⟨hI2, ?_⟩
  calc ∫ m, f (m * x) ∂ν = ∫ m, ∫ g, φ g * f (m * x * g) ∂μ ∂ν := by
        congr 1; funext m; exact hr (m * x)
    _ = ∫ g, ∫ m, φ g * f (m * x * g) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ g, (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) (x * g) ∂μ := by rw [hH]
    _ = ∫ y, (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y) ∂μ :=
        integral_mul_left_eq_self (fun y => (∫ m, f (m * y) ∂ν) * φ (x⁻¹ * y)) x

theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) : Continuous (phe B d) := by
  have he : Continuous B.e := (rowsAut_idem_elementary B).2.2.2
  have hv : ∀ v, Continuous (fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v)) := by
    intro v
    have hc := ((hd v).2.1.2.2.1).2.2 (B.w v)
    exact hc.comp_continuous ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v))
      (fun g => (g v).2)
  have hph : Continuous (ph B d) := by
    unfold ph
    exact continuous_const.mul
      (continuous_star.comp (continuous_finset_prod _ fun v _ => continuous_const.inner (hv v)))
  unfold phe
  exact (hph.comp continuous_fst).mul (he.comp continuous_snd)

theorem one_le_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) : 1 ≤ I.n := by
  rcases Nat.eq_zero_or_pos I.n with h0 | hpos
  · exfalso
    apply hW.1
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    exact absurd i.isLt (by omega)
  · exact hpos

open Classical in

noncomputable def incl (I : AutInst) (v : InfinitePlace I.F) : UJ (I.ε v) →* I.GA :=
  (MonoidHom.inl I.Ginf I.Gf).comp (MonoidHom.mulSingle (fun v => UJ (I.ε v)) v)

theorem isClosedEmbedding_incl (I : AutInst) (v : InfinitePlace I.F) : Topology.IsClosedEmbedding (incl I v) := by
  obtain ⟨hT2, -⟩ := CongTop.adelic_topology I
  haveI := hT2
  classical
  refine Function.LeftInverse.isClosedEmbedding (f := fun p : I.GA => p.1 v) ?_ ?_ ?_
  · intro m
    simp [incl]
  · exact (continuous_apply v).comp continuous_fst
  · exact (continuous_mulSingle (A := fun w : InfinitePlace I.F => UJ (I.ε w)) v).prodMk continuous_const

theorem cusp_of_fixed : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ) (C : ℝ), T y = y → IsContRep B y f → (∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f)) → (∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν → ∀ x, ∫ m, f (m * x) ∂ν = 0) ∧ B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext y) := by
  intro B d h hd hfib hloc hbig T hT y f C hfix hrep hgr
  obtain ⟨hT2, hLC, hSC, -⟩ := CongTop.adelic_topology B.I
  haveI := hT2
  haveI := hLC
  haveI := hSC
  haveI hHaar : (B.I.muA B.μf).IsHaarMeasure := by
    haveI h1 : ∀ w, (muG (B.I.ε w)).IsHaarMeasure := fun w => inferInstance
    haveI h2 : ∀ w, SigmaFinite (muG (B.I.ε w)) := fun w => inferInstance
    haveI h3 : (Measure.pi fun w => muG (B.I.ε w)).IsHaarMeasure := Measure.pi.isHaarMeasure _
    haveI h4 : SFinite (Measure.pi fun w => muG (B.I.ε w)) := inferInstance
    haveI h5 : SFinite B.μf := inferInstance
    unfold AutInst.muA
    exact Measure.prod.instIsHaarMeasure _ _
  have main : ∀ W, B.I.IsIsot W → ∀ ν : Measure B.I.GA, B.I.IsNQuotMeas W ν →
      ∀ x, ∫ m, f (m * x) ∂ν = 0 := by
    intro W hW ν hνW x
    have hn : 1 ≤ B.I.n := one_le_of_isIsot B.I W hW
    obtain ⟨⟨Φ, hΦi, hΦb⟩, hrepf⟩ := GlobalTheory.T.reproducing_formula_fixedVector_moderateGrowth B d h hd hn hloc hbig T hT y f C hfix hrep hgr
    obtain ⟨hfin, -, hconc, hinvN⟩ := hνW
    haveI := hfin
    obtain ⟨c, hc0, hc⟩ := exists_pos_le_tau1_mul_of_mem_NA_of_isIsot B.I W x hW
    have hbd : ∀ᵐ m ∂ν, ∀ g, ‖phe B d g * f (m * x * g)‖ ≤
        c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g := by
      filter_upwards [mem_ae_iff.mpr hconc] with m hm g
      have ht : c ≤ tau1 B.I (m * x) := hc m hm
      have htpos : 0 < tau1 B.I (m * x) := hc0.trans_le ht
      have hb1 := hΦb (m * x) g
      have hpow : 0 < (tau1 B.I (m * x))⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) :=
        pow_pos (inv_pos.mpr htpos) _
      have hΦ0 : 0 ≤ Φ g := (mul_nonneg_iff_of_pos_left hpow).mp ((norm_nonneg _).trans hb1)
      exact hb1.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (inv_nonneg.mpr htpos.le) (inv_anti₀ hc0 ht) _) hΦ0)
    obtain ⟨hint, heq⟩ := constTerm_repro (B.I.muA B.μf) ν f (phe B d) hrep.1
      (continuous_phe B d hd).measurable x (fun g => c⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * Φ g)
      (hΦi.const_mul _) hbd hrepf
    rw [heq]
    obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    obtain ⟨Wv, hWv, hemb⟩ := RadEmb.radical_embeds B.I W v hW
    obtain ⟨νv, hνv⟩ := exists_isHaarSub_NW (B.I.ε v) Wv
    have hNcl : IsClosed ((nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) := by
      rw [coe_nwSub]
      exact isClosed_NW _ _
    have hνv' : IsHaarSub ((nwSub (B.I.ε v) Wv : Subgroup (UJ (B.I.ε v))) : Set (UJ (B.I.ε v))) νv := by
      rw [coe_nwSub]
      exact hνv
    have hemb' := isClosedEmbedding_incl B.I v
    obtain ⟨hNcl', hHs⟩ := isHaarSub_map_emb (incl B.I v) hemb' _ hNcl νv hνv'
    refine weilVanish B.I.GA (B.I.muA B.μf) _ _ hNcl' hHs (fun z => ∫ m, f (m * z) ∂ν)
      (fun z => phe B d (x⁻¹ * z)) ?_ ?_ ?_ hint ?_
    · exact (StronglyMeasurable.integral_prod_right' (ν := ν)
        (f := fun p : B.I.GA × B.I.GA => f (p.2 * p.1))
        (hrep.1.comp (continuous_snd.mul continuous_fst)).stronglyMeasurable).measurable
    · exact ((continuous_phe B d hd).comp (continuous_const.mul continuous_id)).measurable
    · intro n hn z
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hn
      have hk' : k ∈ NW (B.I.ε v) Wv := by
        rw [← coe_nwSub]
        exact hk
      have hkNA : incl B.I v k ∈ B.I.NA W := hemb k hk'
      have hsh := hinvN (fun m => f (m * z)) (fun γ hγ w => by
        show f (γ * w * z) = f (w * z)
        rw [mul_assoc]
        exact hrep.2.1 γ hγ.1 (w * z)) (incl B.I v k) hkNA
      show ∫ m, f (m * (incl B.I v k * z)) ∂ν = ∫ m, f (m * z) ∂ν
      simpa only [mul_assoc] using hsh
    · intro z
      rw [hemb'.measurableEmbedding.integral_map]
      have hz := hfib v Wv hWv νv hνv x⁻¹ z
      simp only [← mul_assoc]
      exact hz
  refine ⟨main, ?_⟩
  intro W hW ν hνW
  have hae := (ExtContRep.ext_ae_eq_contRep B y f hrep).2.2.2 ν hνW.1
  filter_upwards [hae] with x hx
  rw [integral_congr_ae hx]
  exact main W hW ν hνW x

end GlobalTheory.CuspFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualTrace
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct ENNReal

namespace GlobalTheory.TraceSelfDual

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [Field R] [Algebra F R]
  (ι : Type) [Fintype ι]

noncomputable def traceBilin : LinearMap.BilinForm R (ι → R ⊗[F] E) :=
  LinearMap.mk₂ R (fun x y => ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i))
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum])

theorem traceBilin_apply (x y : ι → R ⊗[F] E) :
    traceBilin R ι x y = ∑ i, Algebra.trace R (R ⊗[F] E) (x i * y i) := rfl

theorem traceBilin_symm (x y : ι → R ⊗[F] E) : traceBilin R ι x y = traceBilin R ι y x := by
  simp only [traceBilin_apply, mul_comm]

variable [NumberField F] [NumberField E]

theorem eq_zero_of_traceBilin {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : ι → R ⊗[F] E)
    (hx : ∀ y, traceBilin R ι x y = 0) : x = 0 := by
  classical
  funext j
  refine GlobalTheory.SelfDualFinite.eq_zero_of_trace R h _ fun c => ?_
  have := hx (Pi.single j c)
  rw [traceBilin_apply, Finset.sum_eq_single j] at this
  · rwa [Pi.single_eq_same, mul_comm] at this
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero, map_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Form

theorem exists_selfDual_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)), (∃ r, psiV F ψ v r ≠ 1) → ∀ (ι : Type) [Fintype ι], ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i))) := by
  intro F E _ _ _ _ _ σ h ψ hψ v hne ι _
  let χ : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)
  have hc : Continuous χ :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖χ t‖ = 1 := fun t => hψ.2.1 _
  exact (GlobalTheory.SelfDualFinite.existsUnique_of_bilin v χ hc hu hne _ (traceBilin (Fv F v) ι)
    (traceBilin_symm _ ι) (eq_zero_of_traceBilin _ ι h)).exists

end GlobalTheory.TraceSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermTranslateByAdaptedLatticeAutomorphismsStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_term_translate_by_adapted_lattice_automorphisms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'), ∀ a ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∃ s : TauC Y u u', s.lam = t.lam ∧ s.lam' = t.lam' ∧ ∃ n ∈ NLam t.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t.lam' (lf D (X.Fu u')), s.lin = n * (a * t.lin * a'⁻¹) * n' := by
  first | exact @GlobalTheory.TransT.trans_main | exact GlobalTheory.TransT.trans_main | (intros; apply GlobalTheory.TransT.trans_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameClassTermCountLeCardAutStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameClass_termCount_le_card_aut : GlobalTheory.TypeAsm.FibCardC := by
  first | exact @GlobalTheory.TypeAsm.FibCard.fibCardC | exact GlobalTheory.TypeAsm.FibCard.fibCardC | (intros; apply GlobalTheory.TypeAsm.FibCard.fibCardC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureLocalUnitaryInvariantStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMap_fibreMeasure_localUnitary_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  first | exact @GlobalTheory.LocalFibreInvariant.fibre_invariant | exact GlobalTheory.LocalFibreInvariant.fibre_invariant | (intros; apply GlobalTheory.LocalFibreInvariant.fibre_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramMapFibreMeasureUnitriangularInvariantStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMap_fibreMeasure_unitriangular_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (u : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → (u.map (sigR (Fv F v) σ)).transpose * (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) * u = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → (fib S).map (fun X b => ∑ c, u c b • X c) = fib S := by
  first | exact @GlobalTheory.FibreUnitri.fibre_unitri_invariant | exact GlobalTheory.FibreUnitri.fibre_unitri_invariant | (intros; apply GlobalTheory.FibreUnitri.fibre_unitri_invariant <;> assumption)
end

