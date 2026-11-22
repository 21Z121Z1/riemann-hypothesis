import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonGaugeBiadditiveOfLogSumActionLinearStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonGaugeBiadditive_of_logSum_actionLinear : AddSt → ActSt → BiaddSt := by
  first | exact @GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act | exact GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act | (intros; apply GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralTranslateDetOneCompact
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_translate_det_one_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (C : Set (GL (Fin N) k)), IsCompact C → ∃ D : Set (GL (Fin N) k), IsCompact D ∧ ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ c ∈ C, ValuativeRel.valuation k ((z * c : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 → z * c ∈ D := by
  first | exact @GlobalTheory.CentreCpt.exists_compact_center_mul | exact GlobalTheory.CentreCpt.exists_compact_center_mul | (intros; apply GlobalTheory.CentreCpt.exists_compact_center_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedOffFinitePrimesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_unramified_off_finite_primes : ∀ (D : D7) (c : (AE D)ˣ →* Circle), Continuous c →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e := by
  first | exact @GlobalTheory.UnrOff.unr_off | exact GlobalTheory.UnrOff.unr_off | (intros; apply GlobalTheory.UnrOff.unr_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumLeFrameNormSqGoodPart
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem GlobalTheory.ClassSumLevel.normAt_sq_of_frame {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K)
    (F : Fin n → K) (h2 : ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2 : ℝ) : ℂ) =
      star (fun i => v.embedding (F i)) ⬝ᵥ (H.map v.embedding *ᵥ fun i => v.embedding (F i)) := by
  have hw : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v F = fun i => v.embedding (F i) := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [← h2, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Formalism.HermitianLatticesTheory.normAt,
    Formalism.HermitianLatticesTheory.fcoord, hw, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

theorem GlobalTheory.ClassSumLevel.dot_smul_sandwich {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (M : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Fin n → ℂ) : star x ⬝ᵥ ((c • (A.conjTranspose * M * A)) *ᵥ x) = c * (star (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x))) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem GlobalTheory.ClassSumLevel.classSum_le_normAt_sq : ∀ (X : Fields) [IsTotallyComplex X.K] (Pr : Primes X) (R : Ranks) (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) (P : LevFam X.E X.K R.r Pr.vGs) (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) (t : TupF TU) (hP : (mtildeGSD W Ch sel t.1 P).Ok), (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.Ok3 1 → ∀ (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K) (F' : (mtildeKGSD W Ch sel t.1).EqFun), F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun → HEq ((mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F') (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r (lvlIdem ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ)).mulVec ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ * ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F))) → ∀ (v : InfinitePlace X.K) (X0 : InfinitePlace X.K → Matrix (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t)) (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t)) ℂ), IsUnit (X0 v).det → ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).HV t).map v.embedding → ((mtildeGSD W Ch sel t.1 P).ipAt hP v F'.1 F'.1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 := by
  intro X _ Pr R W Ch sel S hX v0 TU Xg S0 xiVal trIv P Zs t hP hOk F F' hF' hEq v X0 hdet hframe
  set A := colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv with hA
  have hBH : BlockHyp (A.A.fam.R t) (A.A.fam.lvl P.grp P.chr) A.A.fam.v0 1 := ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
  have hC := GlobalTheory.T.levelIdempotent_mul_levelProj_mul_goodPart_eq _ _ _ _ hBH
  have hres : (mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F' =
      (A.A.fam.R t).S.basis.equivFun.symm ((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F) := by
    have h1 := eq_of_heq hEq
    have h2 : (A.A.fam.R t).S.lvlE (A.A.fam.R t).r (A.A.fam.lvl P.grp P.chr).P (A.A.fam.lvl P.grp P.chr).ψ *ᵥ
        (((A.A.fam.R t).S.lvlPr (A.A.fam.R t).r (A.A.fam.lvl P.grp P.chr).P (A.A.fam.lvl P.grp P.chr).ψ *
          (A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr)) *ᵥ F) = (A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F := by
      refine (Matrix.mulVec_mulVec _ _ _).trans ?_
      rw [← Matrix.mul_assoc]
      exact congrArg (· *ᵥ F) hC
    rw [h1]
    exact congrArg _ h2
  have hD := GlobalTheory.T.classSumMetric_eq_gram_at_infinitePlace (mtildeKGSD W Ch sel t.1) (mtildeKOk W Ch sel t.1 hX)
    (mtildeK_rat W Ch sel t.1 hX) v F'
  have hE := GlobalTheory.T.classSum_principalLevel_eq_card_mul_classSum W Ch sel t.1 P hX v F' hF'
  have hN := GlobalTheory.ClassSumLevel.normAt_sq_of_frame _ X0 v F hframe
  have hV := GlobalTheory.T.goodPart_levelForm_infinitePlace_eq_classSum _ _ _ _ hBH v
  have hcard : (Nat.card (A.A.fam.lvl P.grp P.chr).P : ℂ) = (Nat.card P.grp : ℂ) := rfl
  have hne : (Nat.card P.grp : ℂ) ≠ 0 := by
    rw [← hcard]
    exact_mod_cast (Nat.card_pos (α := (A.A.fam.lvl P.grp P.chr).P)).ne'
  have hy0 : ((mtildeKGSD W Ch sel t.1).toCSD (mtildeKOk W Ch sel t.1 hX)).basis.equivFun
      ((A.A.fam.R t).S.basis.equivFun.symm ((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F)) =
      (A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F := LinearEquiv.apply_symm_apply _ _
  rw [hres, hy0] at hD
  have hN' : ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 : ℝ) : ℂ) =
      star (fun i => v.embedding (F i)) ⬝ᵥ (((A.A.fam.R t).HV (A.A.fam.lvl P.grp P.chr)).map v.embedding *ᵥ
        fun i => v.embedding (F i)) := hN
  rw [hV, hcard] at hN'
  have hy : (fun i => v.embedding (((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F) i)) =
      ((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr)).map v.embedding *ᵥ fun i => v.embedding (F i) := by
    funext i
    exact RingHom.map_mulVec v.embedding _ _ i
  have hD1 : (mtildeKGSD W Ch sel t.1).ipAt (mtildeKOk W Ch sel t.1 hX) v F'.1 F'.1 =
      star (fun i => v.embedding (((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F) i)) ⬝ᵥ
        ((A.A.fam.R t).S.H.map v.embedding *ᵥ
          fun i => v.embedding (((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F) i)) := hD
  rw [hy] at hD1
  have key : ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 : ℝ) : ℂ) =
      (Nat.card P.grp : ℂ)⁻¹ * (mtildeKGSD W Ch sel t.1).ipAt (mtildeKOk W Ch sel t.1 hX) v F'.1 F'.1 := by
    refine hN'.trans ((GlobalTheory.ClassSumLevel.dot_smul_sandwich _ _ _ _).trans ?_)
    exact congrArg _ hD1.symm
  have hP' : (mtildeGSD W Ch sel t.1 P).ipAt hP v F'.1 F'.1 =
      (Nat.card P.grp : ℂ)⁻¹ * (mtildeKGSD W Ch sel t.1).ipAt (mtildeKOk W Ch sel t.1 hX) v F'.1 F'.1 := by
    rw [hE, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hfin : ((mtildeGSD W Ch sel t.1 P).ipAt hP v F'.1 F'.1).re =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 := by
    rw [hP', ← key]
    exact Complex.ofReal_re _
  exact hfin.le
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactFibrationSectionMeasure
section
open MeasureTheory

namespace GlobalTheory.Cusp.Shear

theorem isFundamentalDomain_image_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  intro G _ _ _ _ _ _ Γ N N' hle hn V _ _ _ _ _ Λ s π hs hsc hπc hπmul hπs hker hsadd hsΓ hπΓ
    A B hAm hBm hA hB ν
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he
  have himg : e '' (A ×ˢ B) = e.symm ⁻¹' (A ×ˢ B) := by
    ext n; constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨e.symm n, h, by simp⟩
  have efst : ∀ n : N, (((e.symm n).1 : N') : G) = (n : G) * (s (π n))⁻¹ := fun n => rfl
  have esnd : ∀ n : N, (e.symm n).2 = π n := fun n => rfl
  refine IsFundamentalDomain.mk' ?_ ?_
  · rw [himg]; exact (e.symm.continuous.measurable (hAm.prod hBm)).nullMeasurableSet
  · intro x
    have hmemS : ∀ n : N, n ∈ e '' (A ×ˢ B) ↔ (e.symm n).1 ∈ A ∧ (e.symm n).2 ∈ B := by
      intro n; rw [himg]; rfl
    have hfst : ∀ g : N, (((e.symm (g * x)).1 : N') : G) =
        (g : G) * (s (π g))⁻¹ * (s (π g) * ((x : G) * (s (π x))⁻¹) * (s (π g))⁻¹) := by
      intro g
      rw [efst, hπmul, hsadd]
      simp only [Subgroup.coe_mul]
      group
    have hsnd : ∀ g : N, (e.symm (g * x)).2 = π g + π x := fun g => by rw [esnd, hπmul]
    let c : V → N' := fun w => ⟨s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹,
      hn (s w) (hs w) _ (mul_inv_mem hs hπmul hπs hker x)⟩
    obtain ⟨w, hwB, hwu⟩ := hB (π x)
    obtain ⟨δ, hδA, hδu⟩ := hA (c w)
    have hδΓ : ((δ : N') : G) ∈ Γ := Subgroup.mem_subgroupOf.1 δ.2
    let γ0 : Γ.subgroupOf N := ⟨⟨((δ : N') : G) * s w, N.mul_mem (hle (δ : N').2) (hs w)⟩,
      Subgroup.mem_subgroupOf.2 (Γ.mul_mem hδΓ (hsΓ w w.2))⟩
    have hπγ0 : π (γ0 : N) = w := by
      have h : (γ0 : N) = ⟨((δ : N') : G), hle (δ : N').2⟩ * ⟨s w, hs w⟩ := rfl
      rw [h, hπmul, hπs ⟨s w, hs w⟩ w rfl, (hker _).2 (δ : N').2, zero_add]
    refine ⟨γ0, ?_, ?_⟩
    · show (γ0 : N) * x ∈ _
      rw [hmemS, hsnd, hπγ0]
      refine ⟨?_, hwB⟩
      have h : (e.symm ((γ0 : N) * x)).1 = (δ : N') * c w := by
        apply Subtype.ext
        rw [hfst, hπγ0]
        show ((δ : N') : G) * s w * (s w)⁻¹ * _ = ((δ : N') : G) * (s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹)
        group
      rw [h]; exact hδA
    · intro γ hγ
      have hγ' : (γ : N) * x ∈ e '' (A ×ˢ B) := hγ
      rw [hmemS, hsnd] at hγ'
      obtain ⟨hγA, hγB⟩ := hγ'
      have hγΓ : ((γ : N) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      have hw : (⟨π (γ : N), hπΓ γ hγΓ⟩ : Λ) = w := hwu _ hγB
      have hwv : π (γ : N) = w := congrArg Subtype.val hw
      have hδN' : ((γ : N) : G) * (s w)⁻¹ ∈ N' := hwv ▸ mul_inv_mem hs hπmul hπs hker γ
      let δγ : Γ.subgroupOf N' := ⟨⟨((γ : N) : G) * (s w)⁻¹, hδN'⟩,
        Subgroup.mem_subgroupOf.2 (Γ.mul_mem hγΓ (Γ.inv_mem (hsΓ w w.2)))⟩
      have h : (δγ : N') * c w = (e.symm ((γ : N) * x)).1 := by
        apply Subtype.ext
        rw [hfst, hwv]
        rfl
      have hδe : δγ = δ := hδu δγ (by show (δγ : N') * c w ∈ A; rw [h]; exact hγA)
      have hv : ((γ : N) : G) * (s w)⁻¹ = ((δ : N') : G) := by
        rw [← hδe]
      apply Subtype.ext; apply Subtype.ext
      show ((γ : N) : G) = ((δ : N') : G) * s w
      rw [← hv]; group

end GlobalTheory.Cusp.Shear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupFibration
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.Cusp.Shear

theorem isHaarMeasure_map_prodHomeo : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N]
    [LocallyCompactSpace N'] (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → ∀ (μ : MeasureTheory.Measure V), μ.IsAddHaarMeasure →
      (((MeasureTheory.Measure.haar : MeasureTheory.Measure N').prod μ).map
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker)).IsHaarMeasure := by
  intro G _ _ _ _ _ _ _ Γ N N' _ _ _ hle hn hc hc' V _ _ _ _ _ _ _ _ s π hs hsc hπc hπmul hπs hker hsmul μ hμ
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he_def
  set P : Measure (N' × V) := (Measure.haar : Measure N').prod μ with hP
  set ν : Measure N := P.map e with hν
  haveI := hc'.isMulRightInvariant (Measure.haar : Measure N')
  have hem : Measurable e := e.continuous.measurable
  haveI : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map P e
  haveI : ν.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective

  haveI hR : ν.IsMulRightInvariant := ⟨fun n₀ => by
    set z₀ := e.symm n₀
    have hz₀ : ((n₀ : N) : G) = (z₀.1 : G) * s z₀.2 := by
      rw [← prodHomeo_apply hle hs hsc hπc hπmul hπs hker z₀]; simp [z₀, e]
    let c : V → N' := fun v => ⟨s v * z₀.1 * (s v)⁻¹, hn _ (hs v) _ z₀.1.2⟩
    have hcc : Continuous c := by fun_prop
    let T' : V × N' → V × N' := fun p => (p.1 + z₀.2, p.2 * c p.1)
    have hT' : MeasurePreserving T' (μ.prod (Measure.haar : Measure N')) (μ.prod (Measure.haar : Measure N')) :=
      (measurePreserving_add_right μ z₀.2).skew_product (g := fun v m => m * c v)
        (by apply Continuous.measurable; fun_prop)
        (.of_forall fun v => map_mul_right_eq_self _ _)
    have hT : MeasurePreserving (Prod.swap ∘ T' ∘ Prod.swap) P P :=
      Measure.measurePreserving_swap.comp (hT'.comp Measure.measurePreserving_swap)
    have hcomm : (fun n => n * n₀) ∘ e = e ∘ (Prod.swap ∘ T' ∘ Prod.swap) := by
      funext ⟨m, v⟩
      apply Subtype.ext
      change ((m : G) * s v) * (n₀ : G) = ((m * c v : N') : G) * s (v + z₀.2)
      rw [hz₀, hsmul, Subgroup.coe_mul]
      change _ = (m : G) * (s v * (z₀.1 : G) * (s v)⁻¹) * (s v * s z₀.2)
      group
    rw [hν, Measure.map_map (measurable_mul_const n₀) hem, hcomm, ← Measure.map_map hem hT.measurable, hT.map_eq]⟩
  haveI : IsFiniteMeasureOnCompacts ν.inv := Measure.IsFiniteMeasureOnCompacts.map ν (Homeomorph.inv N)
  haveI : ν.inv.IsOpenPosMeasure := (Homeomorph.inv N).continuous.isOpenPosMeasure_map (Homeomorph.inv N).surjective
  haveI : ν.inv.IsHaarMeasure := {}
  haveI := hc.isMulRightInvariant ν.inv
  have hL : ν.IsMulLeftInvariant := by rw [← Measure.inv_inv ν]; infer_instance
  exact {}

end GlobalTheory.Cusp.Shear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitStepsStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnInclusionIntegral_of_limitSteps : LimActSt → LimPtSt → LimFrameSt → InclSt := by
  first | exact @GlobalTheory.IsoTriv.Incl.inclSt_of_lim | exact GlobalTheory.IsoTriv.Incl.inclSt_of_lim | (intros; apply GlobalTheory.IsoTriv.Incl.inclSt_of_lim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRetractionOfLimitStepsStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnInclusionRetraction_of_limitSteps : LimActSt → LimPtSt → InvSt → RetrSt := by
  first | exact @GlobalTheory.IsoTriv.retrSt_of | exact GlobalTheory.IsoTriv.retrSt_of | (intros; apply GlobalTheory.IsoTriv.retrSt_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUniformBound
section
namespace GlobalTheory.CompactUniformHeightBound

open Filter Topology

theorem height_one_le {E : Type} [Field E] [NumberField E] {a : ℕ}
    (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)) : 1 ≤ GlobalTheory.CuspRep.height y := by
  unfold GlobalTheory.CuspRep.height
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _)

theorem compact_uniform_bound : (let d1 : {E : Type} → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsTotallyComplex E] → {a : ℕ} → (GlobalTheory.CuspRep.GA E a → ℂ) → Prop := @(fun {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (F : GlobalTheory.CuspRep.GA E a → ℂ) ↦ ∀ (g₀ : GlobalTheory.CuspRep.GA E a), ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ᶠ (g : GlobalTheory.CuspRep.GA E a) in nhds g₀, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsTotallyComplex E] {a : ℕ} {F : GlobalTheory.CuspRep.GA E a → ℂ}, d1 F → ∀ {K : Set (GlobalTheory.CuspRep.GA E a)}, IsCompact K → ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ g ∈ K, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N) := by
  intro d1 E _ _ _ a F hF K hK
  have hb : ∀ g₀ : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧
      {g : GlobalTheory.CuspRep.GA E a | ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)),
        ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖
          ≤ C * GlobalTheory.CuspRep.height y ^ N} ∈ 𝓝 g₀ := fun g₀ => hF g₀
  choose C N hC hU using hb
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover _ (fun x _ => hU x)
  refine ⟨∑ x ∈ t, C x, t.sup N, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro g hg y
  obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.mp (hKt hg)
  have h1 := height_one_le y
  calc _ ≤ C x * GlobalTheory.CuspRep.height y ^ N x := hgx y
    _ ≤ (∑ i ∈ t, C i) * GlobalTheory.CuspRep.height y ^ t.sup N :=
      mul_le_mul (Finset.single_le_sum (fun i _ => hC i) hx)
        (pow_le_pow_right₀ h1 (Finset.le_sup hx))
        (pow_nonneg (zero_le_one.trans h1) _) (Finset.sum_nonneg fun i _ => hC i)

end GlobalTheory.CompactUniformHeightBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteDvrPointLiftingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_point_lifting : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (X : Scheme.{0}) (s : X ⟶ Sp O) [IsProper s] (K : Type) [Field K] (g : Sp K ⟶ X) [IsPreimmersion g] (a : O →+* K), Function.Injective a → g ≫ s = spMap a → ∀ d : ℕ, (letI := a.toAlgebra; (d : Cardinal) ≤ Algebra.trdeg O K) → ∃ (T : CDVR) (yt : Sp T.V ⟶ X) (ψ : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b ∧ yt ≫ s = spMap b ∧ spMap (algebraMap T.V T.Fr) ≫ yt = spMap ψ ≫ g ∧ TrdegGe (X.residueField (yt (closedPoint T.V))) d := by
  first | exact @GlobalTheory.FactorDepth.exists_cdvr_centred_trdegGe | exact GlobalTheory.FactorDepth.exists_cdvr_centred_trdegGe | (intros; apply GlobalTheory.FactorDepth.exists_cdvr_centred_trdegGe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviRestriction
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def contLeft : Submodule ℂ (Sm E a) where
  carrier := {f | Continuous f.1 ∧ ∀ γ g, f.1 (ratGL E a γ * g) = f.1 g}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl⟩
  add_mem' := fun {f h} hf hh => ⟨hf.1.add hh.1, fun γ g => by
    change f.1 _ + h.1 _ = f.1 _ + h.1 _
    rw [hf.2, hh.2]⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun γ g => by
    change c • f.1 _ = c • f.1 _
    rw [hf.2]⟩

theorem span_cpt_le_contLeft {φ : Sm E a} (hA : IsAutForm φ) :
    Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ≤ contLeft E a := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  have hc := ContAut.continuous_of_isOpen_stab E a φ hA.level
  refine ⟨hc.comp (continuous_mul_const _), fun γ g => ?_⟩
  change φ.1 (ratGL E a γ * g * _) = φ.1 (g * _)
  rw [mul_assoc, hA.left]

variable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]

def sliceLin (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] {𝓕 : Set (BlockIx a r → Ad E)}
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) (hr : r ≤ a) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) : contLeft E a →ₗ[ℂ] (GA E (a - r) → ℂ) where
  toFun f := slice E μ 𝓕 hr f.1.1 m₁ t κ
  map_add' f h := by
    funext m₂
    exact integral_add (CuspidalL2GL.integrableOn_unip f.2.1 f.2.2 μ h𝓕 _) (CuspidalL2GL.integrableOn_unip h.2.1 h.2.2 μ h𝓕 _)
  map_smul' c f := by
    funext m₂
    exact integral_const_mul c _

theorem slice_kfin : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, IsAutForm φ → ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (ψ : Sm E (a - r)),
      ψ.1 = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)) := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 _ φ hA m₁ t κ ψ hψ
  set V := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hV
  have hfin : FiniteDimensional ℂ V := hA.kfin
  have hle := span_cpt_le_contLeft hA
  let L : V →ₗ[ℂ] (GA E (a - r) → ℂ) := sliceLin μ h𝓕 hr m₁ t κ ∘ₗ Submodule.inclusion hle
  have hR : FiniteDimensional ℂ (LinearMap.range L) := inferInstance
  set S := Submodule.span ℂ (Set.range fun k => cptRep E (a - r) k ψ)
  have hS : S.map (Sm E (a - r)).subtype ≤ LinearMap.range L := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨cptRep E a (κ⁻¹ * blkK hr k * κ) φ, Submodule.subset_span ⟨_, rfl⟩⟩, ?_⟩
    funext g
    change slice E μ 𝓕 hr (cptRep E a (κ⁻¹ * blkK hr k * κ) φ).1 m₁ t κ g =
      ψ.1 (g * infGL E (a - r) (Unitary.toUnits k))
    rw [hψ, slice_mul_cpt]
    unfold slice
    congr 1
    funext x
    change φ.1 (_ * _ * _) = _
    simp only [mul_assoc]
    rfl
  have h1 : FiniteDimensional ℂ (S.map (Sm E (a - r)).subtype) := Submodule.finiteDimensional_of_le hS
  exact Module.Finite.equiv (Submodule.equivMapOfInjective (Sm E (a - r)).subtype Subtype.val_injective S).symm

end GlobalTheory.SliceTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantsMonomialApproximation
section
open scoped Classical

namespace GlobalTheory.FinTrace

noncomputable def dcToOrbit (G : Type) [Group G] (H K : Subgroup G) :
    DoubleCoset.Quotient (H : Set G) (K : Set G) → MulAction.orbitRel.Quotient H (G ⧸ K) :=
  Quotient.lift (fun g : G => (Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) : MulAction.orbitRel.Quotient H (G ⧸ K)))
    (by
      intro a b hab
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
      apply Quotient.sound
      show _ ∈ MulAction.orbit H _
      refine ⟨⟨h⁻¹, H.inv_mem hh⟩, ?_⟩
      show ((h⁻¹ : G) • (QuotientGroup.mk (h * a * k) : G ⧸ K)) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa [mul_assoc] using hk)

theorem dcToOrbit_mk (G : Type) [Group G] (H K : Subgroup G) (g : G) :
    dcToOrbit G H K (Quotient.mk _ g) = Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) := rfl

theorem dcToOrbit_bijective (G : Type) [Group G] (H K : Subgroup G) :
    Function.Bijective (dcToOrbit G H K) := by
  constructor
  · intro q₁ q₂ he
    induction q₁ using Quotient.inductionOn with | h a => ?_
    induction q₂ using Quotient.inductionOn with | h b => ?_
    rw [dcToOrbit_mk, dcToOrbit_mk] at he
    obtain ⟨h, hh⟩ := Quotient.exact he
    change ((h : G) • (QuotientGroup.mk b : G ⧸ K)) = _ at hh
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hh
    apply Quotient.sound
    apply DoubleCoset.rel_iff.2
    refine ⟨(h : G)⁻¹, H.inv_mem h.2, ((h * b)⁻¹ * a)⁻¹, K.inv_mem hh, ?_⟩
    group
  · intro o
    induction o using Quotient.inductionOn with | h x => ?_
    induction x using QuotientGroup.induction_on with | H g => ?_
    exact ⟨Quotient.mk _ g, rfl⟩

theorem sum_doubleCoset_eq_sum_orbit : ∀ (G : Type) [Group G] (H K : Subgroup G) (F : G ⧸ K → ℂ), (∀ h : H, ∀ x : G ⧸ K, F (h • x) = F x) →
    ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart H K (Quotient.out q)) : ℂ)) * F (QuotientGroup.mk (Quotient.out q)) =
      ∑ᶠ a : MulAction.orbitRel.Quotient H (G ⧸ K),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * F (Quotient.out a) := by
  intro G _ H K F hF
  let e := Equiv.ofBijective _ (dcToOrbit_bijective G H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have heq : e q = Quotient.mk _ (QuotientGroup.mk (Quotient.out q) : G ⧸ K) := by
    show dcToOrbit G H K q = _
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hrel : MulAction.orbitRel H (G ⧸ K) (Quotient.out (e q)) (QuotientGroup.mk (Quotient.out q)) := by
    apply Quotient.exact
    rw [Quotient.out_eq, heq]
  obtain ⟨h, hh⟩ := hrel
  rw [← hh, hF]
  congr 2
  have h1 := Nat.card_congr (Classical.choice (stabilizer_equiv_locPart G H K (Quotient.out q)))
  rw [← h1]
  exact_mod_cast (Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel (G := H) (a := h • (QuotientGroup.mk (Quotient.out q) : G ⧸ K))
    (b := (QuotientGroup.mk (Quotient.out q) : G ⧸ K)) (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)).toEquiv).symm
end GlobalTheory.FinTrace
end

