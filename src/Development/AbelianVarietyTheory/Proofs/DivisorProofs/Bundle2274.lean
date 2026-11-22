import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp

theorem fdgram_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = (xᴴ * (G.map τ)ᵀ * x)ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp [RCLike.star_def]
  ring

theorem permM_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) :
    (permM e)ᴴ * M * permM e = M.submatrix e.symm e.symm := by
  ext a b
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← e.symm.sum_comp]
  simp

theorem jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)) := by
  rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, ← Matrix.diagonal_neg]
  rfl

theorem sumElim_sgn {p q r : ℕ} (hcard : r = q + p) (a : Fin r) :
    Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => -1)
        (((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a) =
      -(((sgn q (a : ℕ) : ℝ)) : ℂ) := by
  by_cases h : (a : ℕ) < q
  · have ha : finCongr hcard a = Fin.castAdd p ⟨a, h⟩ := Fin.ext rfl
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inr ⟨a, h⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_castAdd]
      rfl
    rw [hv]
    simp [sgn, h]
  · have hlt := a.isLt
    have ha : finCongr hcard a = Fin.natAdd q ⟨(a : ℕ) - q, by omega⟩ := Fin.ext (by simp; omega)
    have hv : ((finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p)))) a =
        Sum.inl ⟨(a : ℕ) - q, by omega⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, ha, finSumFinEquiv_symm_apply_natAdd]
      rfl
    rw [hv]
    simp [sgn, h]

theorem exists_frame_of_sig {n p q : ℕ} {Gc : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature Gc p q)
    {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} (hA : Aᴴ * Formalism.UG.Jpq p q * A = Gc) :
    ∃ (e : Fin p ⊕ Fin q ≃ Fin n) (x : Matrix (Fin n) (Fin n) ℂ), x.det ≠ 0 ∧ A * x = permM e ∧
      (-(xᴴ * Gc * x))ᵀ = Matrix.diagonal fun a : Fin n => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨L, hl, hr⟩ := GlobalTheory.DecompCompare.frame_inv h hA
  obtain ⟨e0, -⟩ := h
  have hcard : n = q + p := by
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  set π : Fin n ≃ Fin p ⊕ Fin q :=
    (finCongr hcard).trans (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin q) (Fin p))) with hπ
  have hAx : A * (L * permM π.symm) = permM π.symm := by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  refine ⟨π.symm, L * permM π.symm, ?_, hAx, ?_⟩
  · have h1 : (L * permM π.symm) * ((permM π.symm)ᵀ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (permM π.symm), permM_mul_transpose, Matrix.one_mul, hl]
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  · have key : ∀ y : Matrix (Fin n) (Fin n) ℂ, yᴴ * Gc * y = (A * y)ᴴ * Formalism.UG.Jpq p q * (A * y) := fun y => by
      rw [← hA, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [key, hAx, permM_conj, Equiv.symm_symm, jpq_eq_diagonal, Matrix.submatrix_diagonal_equiv,
      Matrix.diagonal_neg, Matrix.diagonal_transpose]
    congr 1
    funext a
    rw [Function.comp_apply, hπ, sumElim_sgn hcard a, neg_neg]

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem exists_ident_frame : ∀ (D : D7) (V : HSp D) (P Q : ℕ), V.SigOK → (∀ τ, V.sig τ = (P, Q)) →
    ∀ A : Frames V, IsFrames V A → ∃ (X₀ : Data D.host.E V.rank) (σ : D.what₂.Tau ≃ X₀.Ψ) (x : Frame X₀.Ψ V.rank)
      (e : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 ≃ Fin V.rank),
      X₀.Gm = -(V.gram)ᵀ ∧ (∀ ρ, (σ ρ).1 = tauE D ρ) ∧ IsOrth X₀ x ∧
        IsIdent (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) X₀.Ψ X₀.Gm x σ A e := by
  intro D V P Q hV hs A hA
  choose e x hdet hAx hg using fun ρ => exists_frame_of_sig (hV (tauE D ρ)) (hA ρ)
  have hrk : V.rank = Q + P := by
    have h := hV D.host.φ₀
    rw [hs] at h
    obtain ⟨e0, -⟩ := h
    have h2 := Fintype.card_congr e0
    simp only [Fintype.card_fin, Fintype.card_sum] at h2
    omega
  have hmapT : ∀ ρ, ((-(V.gram)ᵀ).map (tauE D ρ))ᵀ = -(gramAt D V ρ) := fun ρ => by
    ext a b
    simp [gramAt]
  have hgr : ∀ ρ, ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(V.gram)ᵀ) (x ρ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn Q (a : ℕ) : ℝ) : ℂ) := fun ρ => by
    have h1 := hg ρ
    simp only [hs] at h1
    rw [fdgram_eq, hmapT, Matrix.mul_neg, Matrix.neg_mul]
    exact h1
  have hin : ∀ ρ, tauE D ρ ∈ Formalism.L2.Pj.cmTypeOfSqrt D := fun ρ => by
    rw [Formalism.L2.Pj.mem_cm_type_iff, Formalism.L2.Theta.tauE_sqrtMinusD]
    exact (D.host.φ₀_mem).symm
  have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ Formalism.L2.Pj.cmTypeOfSqrt D ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, hρ⟩ => hρ ▸ hin ρ⟩
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk τ)
    rcases InfinitePlace.mk_eq_iff.1 hρ with h' | h'
    · exact ⟨ρ, h'.symm⟩
    · exact absurd (h' ▸ h) ((Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D _).1 (hin ρ))
  have hinj : Function.Injective (tauE D) := fun _ _ h =>
    (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).1 (by simp only [h])
  obtain ⟨hh, hd, hfg, hsp, -⟩ := GlobalTheory.Member.selfDualLat_neg_gram_transpose D V
  obtain ⟨n, hn, hnint⟩ := GlobalTheory.PrincData.exists_nat_herm_int (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) hfg
  obtain ⟨k, hk, hkint⟩ := GlobalTheory.PrincData.exists_nat_int (-(2 * D.host.xi0))
  obtain ⟨X, hΨ, hG, hp, -, -, -, -, -, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski D.host.E V.rank Q 3
    (3 * n * k) (Formalism.L2.Pj.cmTypeOfSqrt D) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) D.host.xi0 (-(2 * D.host.xi0))
    (Formalism.L2.Pj.cm_type_mem_iff_conj_not_mem D) hh hd (by omega)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      exact ⟨x ρ, hdet ρ, hgr ρ⟩)
    hfg hsp le_rfl (Formalism.L2.Pj.conj_xi0_alt D)
    (by
      obtain ⟨ρ, -⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk D.host.φ₀)
      intro h
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      rw [h] at h1
      simp at h1)
    (Or.inr rfl)
    (fun τ hτ => by
      obtain ⟨ρ, rfl⟩ := (hmem τ).1 hτ
      have h1 := Formalism.L2.Theta.xi_zero_im_pos D ρ
      simp [map_ofNat]
      linarith)
    (by positivity)
    (fun u hu v hv => by
      have e1 : ((3 * n * k : ℕ) : D.host.E) / ((3 : ℕ) : D.host.E) * (-(2 * D.host.xi0)) *
          ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v =
          ((k : D.host.E) * (-(2 * D.host.xi0))) * ((n : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V.gram)ᵀ) u v) := by
        push_cast
        field_simp
      rw [e1]
      exact hkint.mul (hnint u hu v hv))
  let σ : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective (fun ρ => ⟨tauE D ρ, by rw [hΨ]; exact hin ρ⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hmem τ.1).1 (hΨ ▸ τ.2)
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  refine ⟨X, σ, fun τ => x (σ.symm τ), e, hG, fun ρ => rfl, fun τ => ?_, fun ρ => ⟨?_, ?_⟩⟩
  · have hτ : τ.1 = tauE D (σ.symm τ) := (congrArg Subtype.val (σ.apply_symm_apply τ)).symm
    show ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (x (σ.symm τ)) = _
    rw [hG, hp, hτ]
    exact hgr _
  · rw [hA ρ, hG]
    show gramAt D V ρ = -((-(V.gram)ᵀ).map (tauE D ρ))ᵀ
    rw [hmapT, neg_neg]
  · show A ρ * x (σ.symm (σ ρ)) = permM (e ρ)
    rw [σ.symm_apply_apply]
    exact hAx ρ

end GlobalTheory.CovTop.VolUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatSectionValueEqMulDetInv
section
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.FlatValue

theorem exists_reduced_frameRing (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) :
    ∃ (A : TRing K) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), (∀ τ, IsUnit (X τ).det) ∧
      ∀ (T : Type) [CommRing T] [Algebra K T] (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (a : Tˣ),
        (∀ τ, IsUnit (g τ).det) → ∃ k : A.R →ₐ[K] T, (∀ τ, (X τ).map k = g τ) ∧ k (s : A.R) = (a : T) := by
  let p : TRing K := ⟨0, ⊥, Ideal.isRadical_bot⟩
  obtain ⟨A, π, X, s, hA⟩ := GlobalTheory.T.exists_frameRing_over_testRing K J m p
  refine ⟨A, X, s, hA.1, fun T _ _ g a hg => ?_⟩
  let ψ : p.R →ₐ[K] T := Ideal.Quotient.liftₐ ⊥ (MvPolynomial.aeval Fin.elim0) (fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero])
  obtain ⟨k, ⟨-, h1, h2⟩, -⟩ := hA.2 T ψ g a hg
  exact ⟨k, h1, h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exOf_flatWt (hq : Dw.q = 0) (τ : Psi H) (b : E →+* ℂ) (i : Fin (Dw.mult b)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) = if b = τ.1 then -1 else 0 := by
  have hi := i.2
  by_cases h : b (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    refine (wtOf_big _ 0 ⟨b, h⟩ i hp).trans ?_
    simp [flatWt, parWt, Subtype.ext_iff]
  · have hq' : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    omega

theorem evR_mul_det_field (hq : Dw.q = 0) (τ : Psi H) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (K : Type) [Field K] [Algebra c.F K] (z y : FrPt Xo c K) (Y : Mats Dw K) (u : Kˣ) (hY : ∀ b, (Y b).det ≠ 0)
    (h : FrChg (fun b => (Y b)ᵀ) (u : K) z y) : evR Xo c f y * (Y τ.1).det = evR Xo c f z := by
  obtain ⟨G, hG, hev⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c K z _
    (fun b => if b = τ.1 then 1 else 0) (fun _ _ => 0) rfl
    (fun b i => by rw [exOf_flatWt hq]; split_ifs <;> simp) f hf
  simp only [Finset.sum_const_zero] at hG
  have hC : G = MvPolynomial.C (G.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hG.totalDegree_le)
  have h1 := hev y Y u hY h
  have h2 := hev z (fun _ => 1) 1 (fun _ => by simp) (by
    simpa using (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K z z z).1)
  rw [hC] at h1 h2
  simp only [Formalism.L2.LamCM.evalFr, MvPolynomial.eval_C, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq',
    Finset.mem_univ, if_true, Matrix.det_one, ite_self, Finset.prod_const_one, one_mul] at h1 h2
  rw [mul_comm, h1, h2]

theorem exists_evR_mul_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ), ∃ b : c.F, b ≠ 0 ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s
  refine ⟨evR Xo c s.sig P.y₀,
    left_ne_zero_of_mul_eq_one (s.evR_mul_inv P.on (GlobalTheory.FlagTan.fromTest_of_isLocalRing _)), ?_⟩
  obtain ⟨A, X, t, hX, hA⟩ := exists_reduced_frameRing c.F (E →+* ℂ) Dw.mult
  haveI : _root_.IsReduced A.R := (Ideal.isRadical_iff_quotient_reduced _).1 A.rad
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.FlagTan.exists_frMap (Algebra.ofId c.F A.R) P.y₀
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A.R w₀ (fun b => (X b)ᵀ) t
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  have step : ∀ (S : Type) [CommRing S] [Algebra c.F S] (k : A.R →ₐ[c.F] S) (z y : FrPt Xo c S),
      FrMap (Algebra.ofId c.F S) P.y₀ z → (FrMap k w y ↔ FrChg (fun b => ((X b).map k)ᵀ) (k t) z y) := by
    intro S _ _ k z y hz
    have h0 : FrMap k w₀ z := GlobalTheory.FlagTan.frMap_of_comp hw₀ hz fun a => k.commutes a
    exact GlobalTheory.FlagTan.frMap_iff_frChg hw h0
  have nat : ∀ (S : Type) [CommRing S] [Algebra c.F S] (k : A.R →ₐ[c.F] S) (y : FrPt Xo c S), FrMap k w y →
      evR Xo c s.sig y = k (evR Xo c s.sig w) := fun S _ _ k y h =>
    GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c s.sig s.sig_mem.1 k w y h
  have univ : evR Xo c s.sig w * (X τ.1).det = algebraMap c.F A.R (evR Xo c s.sig P.y₀) := by
    rw [← sub_eq_zero]
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    let K : Type := q.ResidueField
    let k : A.R →ₐ[c.F] K := IsScalarTower.toAlgHom c.F A.R K
    obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap (Algebra.ofId c.F K) P.y₀
    obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frMap k w
    have hd : ∀ b, ((X b).map k).det = k (X b).det := fun b => (AlgHom.map_det k (X b)).symm
    have h1 := evR_mul_det_field hD.q τ s.sig_mem K z y (fun b => (X b).map k)
      (Units.map (k : A.R →* K) t) (fun b => by rw [hd]; exact ((hX b).map k).ne_zero) ((step K k z y hz).1 hy)
    rw [nat K k y hy, GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hz, hd] at h1
    rw [← Ideal.algebraMap_residueField_eq_zero]
    show k _ = 0
    rw [map_sub, map_mul, h1, k.commutes]
    exact sub_self _
  intro S _ _ z y Y u hY hu hz h
  obtain ⟨k, hk, hkt⟩ := hA S Y hu.unit hY
  have hy : FrMap k w y := (step S k z y hz).2 (by
    rw [hkt, IsUnit.unit_spec]
    simpa only [hk] using h)
  rw [nat S k y hy, ← hk τ.1, ← k.commutes, ← univ, map_mul]
  exact congrArg _ (AlgHom.map_det k (X τ.1)).symm

end GlobalTheory.FlatValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointOfCompactFlagSpaceOpenPartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_of_compactFlagSpaceOpenPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] (z : Sp K ⟶ X.YY), ⊤ ≤ z ⁻¹ᵁ flagOpen X → ∃ io : c.F →+* K, letI := io.toAlgebra; ∃ P : FrPt Xo c K, X.ptY P = z := by
  first | exact @GlobalTheory.CompHS.exists_frPt_of_flagOpen | exact GlobalTheory.CompHS.exists_frPt_of_flagOpen | (intros; apply GlobalTheory.CompHS.exists_frPt_of_flagOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelMeasure
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

open MeasureTheory Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MassFullLevel

theorem levW_le {D : D7} {Tu : Type} (Cl : LevCh D Tu) (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) :=
  fun _ hx => ⟨hx.1, Subgroup.mem_top _⟩

theorem relIndex_ne_zero {D : D7} {Tu : Type} (Cl : LevCh D Tu) (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) ≠ 0 := by
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full _ _ _) = parLev D.sp.cm (Wc D i).gram (Cl.βW i) (Cl.datWp i P) := by
    have e : Cl.datWp i (LevelP.full _ _ _) = { Cl.datWp i P with P := LevelP.full (Cl.datWp i P).Pg (Cl.datWp i P).r ℂ } := by
      simp only [LevCh.datWp, Formalism.IndefR.Lev.datY, if_true]
    rw [← GlobalTheory.CovTop.LevelIndex.lev_full, ← e]
  exact (GlobalTheory.CovTop.LevelIndex.relIndex_lev_le D.sp.cm (Wc D i).gram (Cl.βW i) (Cl.datWp i P) _ hB).1

theorem mass_le_of_full : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ∃ μ' : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i)), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) μ' 𝓕 ∧ μ' 𝓕 ≤ μ 𝓕 := by
  intro D Tu Cl t0 _ i P μ 𝓕 hμ
  obtain ⟨ν, hν⟩ := GlobalTheory.LevelMeasure.exists_isMeasLev D (Wc D i) (Cl.βW i) (Cl.datWp i (LevelP.full Cl.Pg D.R.r ℂ))
    (D.sp.W_sig ((i : ℕ) + 1))
  have hne := relIndex_ne_zero Cl i P
  have hmeas : MeasurableSet {g : GA D (Wc D i) | Formalism.IndefR.Lev.finE (Wc D i) g ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P} := by
    haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    exact (GlobalTheory.ParahoricCompact.isOpen_comap_lev (Wc D i) (Cl.βW i) (Cl.datWp i P)).measurableSet
  have e := GlobalTheory.ChainTw.VolScale.scale (Wc D i) (fun _ m => Formalism.IndefR.Lev.IsMinf m) (fun _ _ h => h.1) _ _ μ ν
    (levW_le Cl i P) Formalism.L2.DIV.lev_le_UA hne hmeas hμ.1 hν
  set n : ℝ≥0∞ := ((GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P).relIndex (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) : ℝ≥0∞)
    with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast hne
  have hnt : n ≠ ⊤ := ENNReal.natCast_ne_top _
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  have eν : ν = n⁻¹ • μ := by
    rw [e, smul_smul, ENNReal.inv_mul_cancel hn0 hnt, one_smul]
  refine ⟨ν, ⟨hν, ?_⟩, ?_⟩
  · rw [eν]; exact hμ.2.mono Measure.smul_absolutelyContinuous
  · rw [e, Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le hn1

end GlobalTheory.MassFullLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariantStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ u : X.functionFieldˣ,
    (∀ γ, fnAct ρ γ u = u) → ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  first | exact @GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant | exact GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant | (intros; apply GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalSetMeasureRealSUStabilizer
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem exists_measurableSet_reps_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Γ : Subgroup (GL (Fin r) E)) (ν : Measure (realSU Ψ G)) [ν.IsMulLeftInvariant], (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ γ ∈ Γ, IsUStab G Λ γ) → ∃ S : Set (realSU Ψ G), MeasurableSet S ∧ ν S = covolume (inReal Ψ G Γ) (realSU Ψ G) ν ∧ ∀ s : realSU Ψ G, ∃ δ ∈ Γ, ∃ hδ : embGL Ψ r δ ∈ realSU Ψ G, (⟨embGL Ψ r δ, hδ⟩ : realSU Ψ G) * s ∈ S := by
  intro E _ _ _ r Ψ G Λ Γ ν _ hΨ hfg hsp hΓ
  haveI := GlobalTheory.SUCount.discrete_inReal hΨ G Γ Λ hfg hsp (fun γ hγ x hx => ((hΓ γ hγ).2 x).1 hx)
  haveI := GlobalTheory.countable_of_discrete_subgroup (inReal Ψ G Γ)
  obtain ⟨D, hD, hu, hF⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (inReal Ψ G Γ)
  refine ⟨D, hD, ((hF ν).covolume_eq_volume).symm, fun s => ?_⟩
  obtain ⟨g, hg, -⟩ := hu s
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hmem : embGL Ψ r δ ∈ realSU Ψ G := e ▸ g.1.2
  refine ⟨δ, hδ, hmem, ?_⟩
  have hg' : ((g : realSU Ψ G)) = ⟨embGL Ψ r δ, hmem⟩ := Subtype.ext e.symm
  rw [← hg']
  exact hg

end GlobalTheory.CovTop.VolUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM

theorem exists_isGaloisCover_of_isQProjOver_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0}) (s : X ⟶ Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K), π ≫ sY = s ∧ IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ _ X s Ga _ _ ρ hs h1 hm hρ hfree
  let τ := autOfRightAction ρ h1 hm
  have := OrbitsInAffineOpens.of_isQProjOver hs τ
  obtain ⟨_, _, _⟩ := isSeparated_finiteType_of_isQProjOver hs
  have hτ : ∀ a, (τ a).hom ≫ s = s := fun a ↦ hρ a⁻¹
  have hf : IsFreeAction τ := .of_isAlgClosed fun k _ _ y a h ↦ inv_eq_one.mp (hfree k y a⁻¹ h)
  refine ⟨finiteQuotient τ, finiteQuotient.π τ, finiteQuotient.desc τ s hτ,
    finiteQuotient.π_desc τ s hτ, ⟨‹_›, h1, hm, fun a ↦ ?_,
      finiteQuotient.isFinite_π_of_isFreeAction hf, finiteQuotient.etale_π hf, inferInstance,
      fun k _ _ y y' e ↦ ?_⟩, inferInstance, inferInstance, inferInstance⟩
  · have := finiteQuotient.comp_π τ a⁻¹
    rwa [autOfRightAction_hom, inv_inv] at this
  · obtain ⟨a, ha⟩ := (finiteQuotient.comp_π_eq_iff τ y y').mp e
    have ha : y ≫ ρ a⁻¹ = y' := ha
    refine ⟨a⁻¹, ha, fun c hc ↦ ?_⟩
    have hc : y ≫ ρ c = y' := hc
    have : y ≫ ρ (c * a) = y := by
      rw [hm, reassoc_of% hc, ← ha, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
    exact eq_inv_of_mul_eq_one_left (hfree k y _ this)

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChartStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generatingFrame_unit_change_to_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  first | exact @GlobalTheory.KeyFramePoint.exists_keyAt_units | exact GlobalTheory.KeyFramePoint.exists_keyAt_units | (intros; apply GlobalTheory.KeyFramePoint.exists_keyAt_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFormParameterOfDiscreteNormsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralForm_parameter_of_discreteNorms : ∀ (C : Type) [NormedField C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) (t : C), N.Int q → t ≠ 0 → ‖t‖ < 1 → (∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖t‖ ^ n) → ∀ m : ℕ, 1 ≤ m → ∃ (β : N.Form (m ^ 2)) (π : C), π ≠ 0 ∧ ‖π‖ < 1 ∧ (∀ n : ℕ, {α | (β.be α α / (2 * m ^ 2)).toNat = n}.Finite) ∧ ∀ α, Real.exp (-(q α / (m : ℝ) ^ 2)) = ‖π‖ ^ (β.be α α / (2 * m ^ 2)).toNat := by
  first | exact @GlobalTheory.MBLow.exists_form_of_discrete_norms | exact GlobalTheory.MBLow.exists_form_of_discrete_norms | (intros; apply GlobalTheory.MBLow.exists_form_of_discrete_norms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIsoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jacobian_section_isUnit_germ_of_localIso : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (p : Y ⟶ Sp F) (σ : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d p] [SmoothOfRelativeDimension d (σ ≫ p)] (K : CanonLB p d) (K' : CanonLB (σ ≫ p) d),
    ∃ J : H0 (σ ≫ p) (LB.div K'.bundle (K.bundle.pull σ)) ⊤, ∀ x : X, Function.Bijective (σ.stalkMap x).hom →
      ∀ (a : (LB.div K'.bundle (K.bundle.pull σ)).ι) (ha : x ∈ (LB.div K'.bundle (K.bundle.pull σ)).U a),
        IsUnit (H0.germ a x (memTop x) ha J) := by
  first | exact @GlobalTheory.exists_jacobian_section_isUnit_germ | exact GlobalTheory.exists_jacobian_section_isUnit_germ | (intros; apply GlobalTheory.exists_jacobian_section_isUnit_germ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeLieBasisChangeDetPowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatumBaseChange_lieBasisChange_detPow : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R : Type) [CommRing R] (y : KeyIn R) (x : KeyIn ℂ) (f : R →+* ℂ), KeyPB x y f → ∀ (v' : Fin y.P.g → (epsR R ⟶ y.P.A)) (hv' : IsLieBasis v') (M : Matrix (Fin y.P.g) (Fin y.P.g) R), (∀ i, IsLieComb (M i) y.v (v' i)) → ∃ x' : KeyIn ℂ, KeyPB x' ⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'⟩ f ∧ (κ ℂ x' : ℂ) = (M.map f).det ^ 4 * κ ℂ x := by
  first | exact @GlobalTheory.KeyLieChg.exists_keyPB_det | exact GlobalTheory.KeyLieChg.exists_keyPB_det | (intros; apply GlobalTheory.KeyLieChg.exists_keyPB_det <;> assumption)
end

