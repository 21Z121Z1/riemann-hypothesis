import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0050
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0491
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRational
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemHROfGram
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WittS

section Abstract

variable {A B : Type} [CommRing A] [CommRing B]

theorem map_mul_of_mul (Q : B →+ A) (hQ : ∀ y y', Q (y * y') = Q y * Q y')
    {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B) :
    (X * Y).map Q = X.map Q * Y.map Q := by
  ext i j
  simp [Matrix.mul_apply, map_sum, hQ]

theorem exists_lift {m : Type} [Fintype m] [DecidableEq m] (c : A →+* A) (s : B →+* B) (P : A →+* B)
    (Q : B →+ A) (e : A) (hQs : ∀ y, Q (s y) = c (Q y)) (hQP : ∀ x, Q (P x) = e * x)
    (hQ : ∀ y y', Q (y * y') = Q y * Q y') (J : Matrix m m A) (g g' : Matrix m m B)
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) (hU : (g.map s)ᵀ * J.map P * g = J.map P) :
    ∃ h h' : Matrix m m A, h * h' = 1 ∧ h' * h = 1 ∧ (h.map c)ᵀ * J * h = J ∧
      e • (h - 1) = h - 1 ∧
      ∀ (ι : Type) (N N' : Matrix m ι A), e • N = N → e • N' = N' → g * N.map P = N'.map P →
        h * N = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hQe : ∀ y, e * Q y = Q y := fun y => by rw [← hQ1, ← hQ, one_mul]
  have hee : e * e = e := by simpa [hQ1] using hQe 1
  have hce : c e = e := by rw [← hQ1, ← hQs, map_one]
  have hGe : ∀ {a b : Type} (X : Matrix a b B), e • X.map Q = X.map Q := by
    intro a b X
    ext i j
    simp [hQe]
  have hfz : ∀ {a b : Type} (X : Matrix a b B), (1 - e) • X.map Q = 0 := by
    intro a b X
    rw [sub_smul, one_smul, hGe, sub_self]
  have h1Q : (1 : Matrix m m B).map Q = e • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hQ1]
    · simp [Matrix.one_apply_ne hij]
  have hPQ : ∀ {a b : Type} (X : Matrix a b A), (X.map P).map Q = e • X := by
    intro a b X
    ext i j
    simp [hQP]
  have hfe : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
  have hef : e * (1 - e) = 0 := by linear_combination -hee
  have hsum : ∀ {a b : Type} (X : Matrix a b A), e • X + (1 - e) • X = X := by
    intro a b X
    rw [← add_smul]
    simp
  have hmul : ∀ {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B),
      (X * Y).map Q = X.map Q * Y.map Q := fun X Y => map_mul_of_mul Q hQ X Y
  have hinv : ∀ u v : Matrix m m B, u * v = 1 →
      (u.map Q + (1 - e) • 1) * (v.map Q + (1 - e) • 1) = 1 := by
    intro u v huv
    rw [add_mul, mul_add, mul_add, ← hmul, huv, h1Q]
    simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hfz, smul_smul, hfe, add_zero,
      zero_add]
    exact hsum 1
  have hstar : ((g.map Q + (1 - e) • (1 : Matrix m m A)).map c)ᵀ =
      ((g.map s)ᵀ).map Q + (1 - e) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hQs, hce]
    · simp [hQs, hce, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  refine ⟨g.map Q + (1 - e) • 1, g'.map Q + (1 - e) • 1, hinv _ _ hgg', hinv _ _ hg'g, ?_, ?_, ?_⟩
  · rw [hstar]
    have hJ : ((g.map s)ᵀ).map Q * J * g.map Q = e • J := by
      have h0 : ((g.map s)ᵀ).map Q * (e • J) = ((g.map s)ᵀ).map Q * J := by
        rw [mul_smul_comm, ← smul_mul_assoc, hGe]
      rw [← h0, ← hPQ J, ← hmul, ← hmul, hU]
    have hL : (1 - e) • (((g.map s)ᵀ).map Q * J) = 0 := by
      rw [← smul_mul_assoc, hfz, zero_mul]
    have hR : (1 - e) • (J * g.map Q) = 0 := by
      rw [← mul_smul_comm, hfz, mul_zero]
    simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hJ, hL, hR,
      smul_smul, hfe, add_zero, zero_add]
    exact hsum J
  · have h1 : g.map Q + (1 - e) • (1 : Matrix m m A) - 1 = g.map Q - e • 1 := by
      rw [sub_smul, one_smul]
      abel
    rw [h1, smul_sub, hGe, smul_smul, hee]
  · intro ι N N' hN hN' hg
    have hz : (1 - e) • N = 0 := by
      rw [sub_smul, one_smul, hN, sub_self]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hz, add_zero]
    have h2 : g.map Q * N = g.map Q * (e • N) := by rw [hN]
    rw [h2, ← hPQ N, ← hmul, hg, hPQ, hN']

end Abstract

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_mem_HR_of_gram (σ : E →ₐ[F] E) (hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J)
    (Ad : Type) [CommRing Ad] [Algebra F Ad] (R : Type) [CommRing R] [Algebra F R]
    [IsArtinianRing R] [IsReduced R] (e : Ad ⊗[F] E)
    (P : Ad ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ Ad ⊗[F] E)
    (hPinc : ∀ x, P (inclR Ad x) = inclR R x)
    (hPc : ∀ x, P (sigR Ad σ x) = sigR R σ (P x))
    (hQs : ∀ y, Q (sigR R σ y) = sigR Ad σ (Q y)) (hPQ : ∀ y, P (Q y) = y)
    (hQP : ∀ x, Q (P x) = e * x) (hQm : ∀ y y', Q (y * y') = Q y * Q y')
    (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι E) (hΓ : Γ.det ≠ 0)
    (N N' : Matrix (Fin M) ι (Ad ⊗[F] E)) (hN : e • N = N) (hN' : e • N' = N')
    (hG : (HMul.hMul (N.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad))
    (hG' : (HMul.hMul (N'.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N' : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad)) :
    ∃ h : HR Ad σ J, e • ((h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1) =
        (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1 ∧
      (HMul.hMul (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hPe : P e = 1 := by rw [← hQ1, hPQ]
  let eqv := Fintype.equivFin ι
  have gramX : ∀ N₀ : Matrix (Fin M) ι (Ad ⊗[F] E),
      (HMul.hMul (N₀.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N₀ : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad) →
      gramR R σ J (fun a i => P (N₀ i (eqv.symm a))) =
        (Γ.submatrix eqv.symm eqv.symm).map (inclR R) := by
    intro N₀ h₀
    ext a b
    have h := congrArg (fun X : Matrix ι ι (Ad ⊗[F] E) => P (X (eqv.symm a) (eqv.symm b))) h₀
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, hPc, hPe, one_mul, hPinc, Finset.mul_sum] at h
    simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.submatrix_apply, mul_assoc]
    exact h
  have hXY := (gramX N hG).trans (gramX N' hG').symm
  have hdet : IsUnit (gramR R σ J (fun a i => P (N i (eqv.symm a)))).det := by
    rw [gramX N hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self]
    exact (isUnit_iff_ne_zero.mpr hΓ).map _
  obtain ⟨hU, hact⟩ := GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq F E σ hCM M J hJ R _ _ _
    hXY hdet
  let g : GL (Fin M) (R ⊗[F] E) := HeckeCharacterZeroLocus.SiegelWeilU.HA.mat R σ J hU
  have hJP : (J.map (inclR Ad)).map P = J.map (inclR R) := by
    ext i j
    simp [hPinc]
  have hmem : ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (sigR R σ))ᵀ *
      (J.map (inclR Ad)).map P * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J.map (inclR Ad)).map P := by
    rw [hJP]
    let h' : HeckeCharacterZeroLocus.SiegelWeilU.HR R σ J := hU
    exact h'.2
  have hgN : (HMul.hMul (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (N.map P) : Matrix (Fin M) ι (R ⊗[F] E)) = N'.map P := by
    ext i k
    have := congrFun (congrFun hact (eqv k)) i
    simpa [GlobalTheory.CompanionTheory.SW.actW, HeckeCharacterZeroLocus.SiegelWeilU.actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply, g]
      using this
  obtain ⟨h, h', h1, h2, h3, h4, h5⟩ := exists_lift (sigR Ad σ) (sigR R σ) P Q e hQs hQP hQm
    (J.map (inclR Ad)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (by simp) (by simp) hmem
  let u : GL (Fin M) (Ad ⊗[F] E) := ⟨h, h', h1, h2⟩
  have hu : u ∈ HR Ad σ J := h3
  exact ⟨⟨u, hu⟩, h4, h5 ι N N' hN hN' hgN⟩

end General

theorem exists_unitary_off_S : (∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R) (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D), (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧ (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧ ∀ y y', Q (y * y') = Q y * Q y') → ∀ (D : D7) (V : HSp D) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι D.host.E), Γ.det ≠ 0 → ∀ N N' : Matrix (Fin V.rank) ι (AE D), e • N = N → e • N' = N' → (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → (HMul.hMul (N'.map (cA D))ᵀ (HMul.hMul (gA V) N' : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → ∃ h : GA D V, e • (mt V h - 1) = mt V h - 1 ∧ (HMul.hMul (mt V h) N : Matrix (Fin V.rank) ι (AE D)) = N' := by
  intro H D V S e he ι _ _ Γ hΓ N N' hN hN' hG hG'
  obtain ⟨R, _, _, _, _, P, Q, hPinc, hPc, hQs, hPQ, hQP, hQm⟩ := H D S e he
  obtain ⟨h, h1, h2⟩ := exists_mem_HR_of_gram D.sp.cm.sig (isCMExt_host D) V.gram (isHermND_gram V)
    (AF D.host.F) R e P Q hPinc hPc hQs hPQ hQP hQm ι Γ hΓ N N' hN hN' hG hG'
  exact ⟨h, h1, h2⟩

end GlobalTheory.CompanionTheory.WittS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegativeSchwartzBump
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicBump

open NumberField IsDedekindDomain Topology
open scoped Classical

theorem exists_compact_open_nhds (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {w₀ : κ → FiniteAdeleRing (𝓞 F) F} {B : Set (κ → FiniteAdeleRing (𝓞 F) F)} (hB : B ∈ 𝓝 w₀) :
    ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsOpen C ∧ IsCompact C ∧ IsClosed C ∧ w₀ ∈ C ∧ C ⊆ B := by
  rw [nhds_pi, Filter.mem_pi] at hB
  obtain ⟨I, -, t, ht, hsub⟩ := hB
  have hO : (⋂ i, (fun a => w₀ i + a) ⁻¹' t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    Filter.iInter_mem.mpr fun i =>
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht i)
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  have hNF : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, mul_inv_cancel₀ hNF, map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F :=
    { toFun := fun u => c * u
      invFun := fun u => (N : FiniteAdeleRing (𝓞 F) F) * u
      left_inv := fun u => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u) = u
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u) = u
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  let D : κ → Set (FiniteAdeleRing (𝓞 F) F) := fun i =>
    (Homeomorph.subRight (w₀ i)) ⁻¹' (h ⁻¹' (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)))
  have hDc : ∀ i, IsCompact (D i) := fun i =>
    (Homeomorph.subRight (w₀ i)).isCompact_preimage.2 (h.isCompact_preimage.2 hint_c)
  have hDo : ∀ i, IsOpen (D i) := fun i =>
    (hint_o.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  have hint_l : IsClosed (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (Formalism.UG.intAd F).toAddSubgroup.isClosed_of_isOpen hint_o
  have hDl : ∀ i, IsClosed (D i) := fun i =>
    (hint_l.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  refine ⟨Set.univ.pi D, isOpen_set_pi Set.finite_univ fun i _ => hDo i, isCompact_univ_pi hDc,
    isClosed_set_pi fun i _ => hDl i, fun i _ => ?_, fun u hu => hsub fun i _ => ?_⟩
  · show c * (w₀ i - w₀ i) ∈ (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))
    rw [sub_self, mul_zero]
    exact zero_mem (Formalism.UG.intAd F)
  · have hi : c * (u i - w₀ i) ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have h1 := Set.mem_iInter.mp (hNO _ hi) i
    rw [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at h1
    simpa using h1

theorem exists_bump : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : Set (κ → AF F)), IsOpen N → ∀ z₀ ∈ N, ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N → Φ z = 0) ∧ 0 < (Φ z₀).re := by
  intro F _ _ κ _ N hN z₀ hz₀
  let P : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hP : Continuous P := continuous_pi fun i =>
    Continuous.prodMk ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst))
      ((continuous_apply i).comp continuous_snd)
  let y₀ : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1
  let w₀ : κ → FiniteAdeleRing (𝓞 F) F := fun i => (z₀ i).2
  have hPz : ∀ z : κ → AdeleRing (𝓞 F) F,
      P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) = z := fun z =>
    funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  have hmem : P ⁻¹' N ∈ 𝓝 (y₀, w₀) :=
    (hN.preimage hP).mem_nhds (by show P (y₀, w₀) ∈ N; rw [hPz z₀]; exact hz₀)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (E := κ → mixedEmbedding.mixedSpace F) (n := ⊤) hA
  obtain ⟨C, hCo, hCc, hCcl, hwC, hCB⟩ := exists_compact_open_nhds F hB
  have hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ) :=
    hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)
  have hf : ∀ y, f y = ((φ y : ℝ) : ℂ) := fun y => rfl
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator C fun _ => 1
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hCc fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ C
    · exact ⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by
        simp only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩
  have hval : ∀ z, GlobalTheory.WeilM.pureA F f g z = ((φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) : ℝ) : ℂ) *
      g (fun i => (z i).2) := fun z => rfl
  have hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ) := fun w => by
    by_cases hw : w ∈ C <;> simp [g, hw]
  have hnn : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  refine ⟨GlobalTheory.WeilM.pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, fun z => ?_, fun z hz => ?_, ?_⟩
  · rw [hval, hgval, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩
  · rw [hval]
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have h1' : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) ≠ 0 := fun h => h1 (by rw [h]; simp)
    have h2' : (fun i => (z i).2) ∈ C := by
      by_contra h
      exact h2 (Set.indicator_of_notMem h _)
    have h3 := hAB (Set.mk_mem_prod (hφs (subset_tsupport _ h1')) (hCB h2'))
    apply hz
    have h4 : P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) ∈ N := h3
    rwa [hPz z] at h4
  · rw [hval]
    have e1 : g (fun i => (z₀ i).2) = 1 := Set.indicator_of_mem (show w₀ ∈ C from hwC) _
    have e2 : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1) = 1 := hφ1
    rw [e1, e2]
    simp

end GlobalTheory.CompanionTheory.AdelicBump

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorInduction
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact fun h => hPQ _ _ h
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem factorStep_holds : FactorStep := by
  intro h4 E _ _ _ N W hW
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, fun K _ =>
      ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, ?_⟩⟩
    intro U _ _ _ _ _ _ hU
    obtain ⟨ψ, hψ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    refine ⟨.leaf ⊤ 0, LinearMap.id, trivial, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl,
      fun _ _ _ => rfl, fun χ _ => ?_, ψ, hψ, hne⟩
    exact ⟨(mulChi 0 (Model.absC E 0)).symm χ, trivial, by simp⟩
  · obtain ⟨Ω, hΩ, h⟩ := h4 E N W hW
    refine ⟨Ω, hΩ, fun K hK => ?_⟩
    obtain ⟨Θ, hΘ, h'⟩ := h K hK
    refine ⟨Θ, hΘ, ?_⟩
    intro U hs ha hg hn hc hi hU
    obtain ⟨t, T, hG, hL, he, hm, hne⟩ := h' U hN hs ha hg hn hc hi hU
    exact ⟨t, T, red_of_leaves hL, hG, allLeaves_mono (fun M V h => Or.inr h.2) hL, he, hm, hne⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLimit
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.FactorLimProof

theorem multiset_eq_of_prod_shift {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' :=
  by apply _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep <;> assumption

theorem factorLim_of_parts : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound →
    GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts →
    GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  intro _ hLT hLB hCI hIE hCE hMF hTS hGr hIT E _ _ _ Θs Θf Ωs Ωf N t ψ m n B hLim hRA hRed hGood hAll hψ hψ0 hCap hB hCl
  have leaf := fun k => hLB E N (t k) (ψ k) (m k) B hIT (hGood k) (hψ k) (hψ0 k) (hCap k) (hB k)
  obtain ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, hEmb⟩ :=
    hLT hTS hGr E Θs Θf Ωs Ωf N hLim hRA N le_rfl t (2 * B) hRed hGood hAll leaf
  refine ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, fun τ => ?_, hEmb⟩
  obtain ⟨m₀, mk, hs, hk, hprod⟩ := hCI E N t' s τ hConv hGs
  have hst : ∀ k, IsStable (t (φ k)).space := fun k =>
    hTS E N _ (disc_stable (good_disc (hGood _)))
  have hmk : ∀ k, mk k = m (φ k) τ := by
    intro k
    obtain ⟨e, he1, he2, he3⟩ := hEmb k
    have hne : e (ψ (φ k)) ≠ 0 := fun h => hψ0 _ (he2 _ (hψ _) h)
    have hc : CapEig (e (ψ (φ k))) (m (φ k)) := hCE E N _ e _ _ (hst k) he3 (hψ _) (hCap _)
    exact hIE E N (t' k) _ _ τ _ hIT (hk k) (he1 _ (hψ _)) hne hc
  have hlim : ∀ u : ℂ, Tendsto (fun k => ((m (φ k) τ).map (u + ·)).prod) atTop
      (𝓝 (((n τ).map (u + ·)).prod)) := fun u =>
    hMF.2.2 (fun k => m (φ k) τ) (n τ)
      (fun ε hε => hφ.tendsto_atTop.eventually (hCl τ ε hε)) u
  have hm₀ : m₀ = n τ := multiset_eq_of_prod_shift fun u =>
    tendsto_nhds_unique (by simpa only [hmk] using hprod u) (hlim u)
  exact hm₀ ▸ hIT E N s τ m₀ hs

end GlobalTheory.CompanionTheory.EGlue.FactorLimProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CjEx

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjAbove {v : PlF E} (w : Above v) : Above v :=
  ⟨conjSrc (IsCMField.complexConj E).toRingEquiv w.1,
    (GlobalTheory.DefU.LocRet.under_conjSrc (E := E) w.1).trans w.2⟩

def cj (v : PlF E) : Av v →+* Av v :=
  RingHom.pi fun w => (conjLoc (IsCMField.complexConj E).toRingEquiv w.1 : _ →+* _).comp
    (Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) (conjAbove w))

theorem continuous_cj (v : PlF E) : Continuous (cj v) :=
  continuous_pi fun w => (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w.1).1.comp (continuous_apply (conjAbove w))

theorem projv_conjFin (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj v (projv v x) :=
  funext fun _ => pLoc_conjFin _ _ _

end GlobalTheory.CompanionTheory.CjEx

theorem GlobalTheory.CompanionTheory.CjEx.cjEx : PositivityTheory.Rg.BcB.G8.Fin.CjEx := fun _ _ _ _ v =>
  ⟨GlobalTheory.CompanionTheory.CjEx.cj v, GlobalTheory.CompanionTheory.CjEx.continuous_cj v, GlobalTheory.CompanionTheory.CjEx.projv_conjFin v⟩

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteEulerProductOf
section
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

namespace GlobalTheory.CompanionTheory.EulerAsm

theorem exists_above {E : Type} [Field E] [NumberField E] [IsCMField E] (v : PlF E) :
    ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨Q, hQm.isPrime, hQ0⟩, ?_⟩
  apply HeightOneSpectrum.ext
  exact (hQo.over).symm

theorem eulerFinOf' : EulerFinOf' := by
  intro hC hR hG hL hH hI E _ _ _ hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  obtain ⟨hr, hth, hK, hKm⟩ := hR hC E a b
  have hKeq : (Kf E a).prod (Kf E b) = ⨅ v, (Kv (E := E) a b v).comap (pv a b v) := by
    ext x
    rw [Subgroup.mem_iInf]
    exact hKm x
  obtain ⟨H1, H2, H3, H4, H5⟩ := hH hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2
  have main := GlobalTheory.T.twistedOrbitalIntegral_restrictedProduct_finprod (pv (E := E) a b) (Kv a b) hr (thP E a b) (thv a b) hth hK
    (ratF E a δ₁, ratF E b δ₂) (finFn S φ₁ φ₂) (fv S φ₁ φ₂) (hG E a b S hS φ₁ φ₂ h1 h2) H1 H2 H3 H4 H5
  rw [hKeq, main, hI E S hS]
  refine finprod_congr fun v => ?_
  have key : ∀ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v →
      twOrb (thv a b v) (Kv a b v) (pv a b v (ratF E a δ₁, ratF E b δ₂)) (fv S φ₁ φ₂ v) =
        twOrb ((thL a w).prodMap (thL b w)) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) (seen φ₁ φ₂ w) := by
    rintro w hw rfl
    exact hL hC E hU a b S hS φ₁ φ₂ h1 h2 δ₁ δ₂ e1 e2 w hw
  obtain ⟨w0, hw0⟩ := exists_above v
  have h : ∃ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) = v := by
    obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w0
    exact ⟨u, huS, hu.trans hw0⟩
  simp only [secPl, dif_pos h, Option.elim]
  exact key _ h.choose_spec.1 h.choose_spec.2

end GlobalTheory.CompanionTheory.EulerAsm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteZSpanIntegralRepresentationStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_z_span_integral_representation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
      (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure],
      ∃ κ : AutomorphicForm.archGroup E a → ℂ, Continuous κ ∧ HasCompactSupport κ ∧
        ∀ g : GA E a, φ.1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * κ y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite | exact GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite | (intros; apply GlobalTheory.CompanionTheory.HCRep.GrowthKernel.exists_kernel_of_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleOfRationalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_of_rational : GlobalTheory.CompanionTheory.MixZ.CycleOfRat := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.CycleRat.cycleOfRat | exact GlobalTheory.CompanionTheory.MixZ.CycleRat.cycleOfRat | (intros; apply GlobalTheory.CompanionTheory.MixZ.CycleRat.cycleOfRat <;> assumption)
end

