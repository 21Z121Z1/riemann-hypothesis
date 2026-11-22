import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0234
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyZeroOfDeRhamCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqOfMemDpcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFrames
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.FrameDom

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.cc]
  exact IsCMField.complexEmbedding_complexConj E τ x

lemma gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma gm_eq {r : ℕ} (G G' : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ v w, herm G (γ.mulVec v) (γ.mulVec w) = herm G' v w) :
    G' = γᵀ * G * γ.map cc := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.single_apply, map_one, map_zero,
    mul_one, one_mul, mul_zero, zero_mul, ite_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.mulVec, dotProduct, apply_ite] at hij
  rw [← hij]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    ReciprocityTheory.ChartRestriction.G.FD.cc]
  rw [Finset.sum_comm]

omit [NumberField E] [IsCMField E] in
lemma det_map_ne {r : ℕ} (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).2 ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

lemma gram_mul {r : ℕ} (G G' : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ v w, herm G (γ.mulVec v) (γ.mulVec w) = herm G' v w) (τ : E →+* ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (γ.map τ * M) = gram τ G' M := by
  have h1 : (γ.map τ * M).map (starRingEnd ℂ) = (γ.map cc).map τ * M.map (starRingEnd ℂ) := by
    rw [Matrix.map_mul]
    congr 1
    ext a b
    simp only [Matrix.map_apply, emb_cc']
  have h2 : (γᵀ * G * γ.map cc).map τ = (γ.map τ)ᵀ * G.map τ * (γ.map cc).map τ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [gram_eq, gram_eq, gm_eq G G' γ h, h2, h1, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem mem_dom_of_isometry :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E), X.p0 = X'.p0 → (∀ τ, τ ∈ X.Ψ ↔ τ ∈ X'.Ψ) → (∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E).mulVec v) ((γ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X'.Gm v w) → ∀ (x : Frame X'.Ψ r) (x' : Frame X.Ψ r), x ∈ X'.dom → (∀ (τ : E →+* ℂ) (h₂ : τ ∈ X'.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ X.dom := by
  intro E _ _ _ r X X' γ hp hΨ hh x x' hx hmat
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.dom, ReciprocityTheory.ChartRestriction.G.FD.GG, Set.mem_ofPred_eq] at hx ⊢
  intro τ
  have h₂ : τ.1 ∈ X'.Ψ := (hΨ τ.1).1 τ.2
  obtain ⟨hdet, hpos⟩ := hx ⟨τ.1, h₂⟩
  have hm := hmat τ.1 h₂ τ.2
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero (det_map_ne τ.1 γ) hdet
  · have hd : dmin X.Gm x' τ i = dmin X'.Gm x ⟨τ.1, h₂⟩ i := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.dmin]
      rw [hm, gram_mul X.Gm X'.Gm (γ : Matrix (Fin r) (Fin r) E) hh]
    rw [hd, hp]
    exact hpos i

end GlobalTheory.FrameDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsBreuilKisinGaloisStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalStab

section Alg
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_mul_eq_smul [IsDomain R] {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • 1) :
    A.det ≠ 0 := by
  have hd : A.det * B.det = c ^ Fintype.card n := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ hc hd.symm

omit [Fintype n] [DecidableEq n] in
theorem map_smul_hom {R' : Type} [CommRing R'] (f : R →+* R') (c : R) (M : Matrix n n R) :
    (c • M).map f = f c • M.map f := by
  ext i j; simp

end Alg

theorem smul_cancel_of_isUnit {R : Type} [CommRing R] {n : Type} {c : R} (hc : IsUnit c) {M M' : Matrix n n R}
    (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact hc.mul_left_cancel this

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem gal_E (bk : BK K) (g : GQ l) : ∃ w : (Ainf l)ˣ, Per.σA g (bk.ev bk.E) = bk.ev bk.E * w := by
  have key : ∀ h : GQ l, bk.ev bk.E ∣ Per.σA h (bk.ev bk.E) := fun h => by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  have h2 : Per.σA g (bk.ev bk.E) ∣ bk.ev bk.E := by
    have := map_dvd (Per.σA g) (key g⁻¹)
    rwa [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one] at this
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd (key g) h2
  exact ⟨w, hw.symm⟩

theorem frob_zl (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  rw [WittVector.frobenius_eq_map_frobenius]
  exact map_zlW l _ z

theorem σA_frob (g : GQ l) (a : Ainf l) :
    Per.σA g (WittVector.frobenius a) = WittVector.frobenius (Per.σA g a) := by
  apply inclW_injective
  rw [← galW_inclW, ← frobW_inclW, ← frobW_inclW, ← galW_inclW]
  refine WittVector.ext fun n => ?_
  simp [galW, mapAlgEquivW, mapEquivW, frobW, WittVector.map_coeff, frobenius_def, map_pow]

theorem frob_Y (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d N : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (F : Pre bk N d ρ) (M : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (hY : Y.map (inclW l) = inclW l τ ^ M • F.T) :
    bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * F.A.map bk.ev) := by
  apply Matrix.map_injective inclW_injective
  beta_reduce
  have hfτ : frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ := by rw [frobW_inclW, hτ.1, map_mul]
  have h1 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
    ext i j; simp only [Matrix.map_apply, frobW_inclW]
  have hA : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by rw [Matrix.map_map]; rfl
  have hφ : inclW l (bk.ev bk.E) ^ N • F.T.map (frobW l) = F.T * F.A.map bk.evW := F.φ
  have h2 : (inclW l τ ^ M • F.T).map (frobW l) = (inclW l (bk.ev bk.E) * inclW l τ) ^ M • F.T.map (frobW l) := by
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hfτ]
  rw [map_smul_hom, map_smul_hom, h1, Matrix.map_mul, hY, h2, hA, Matrix.smul_mul,
    ← hφ, smul_smul, smul_smul, smul_smul, map_pow, map_pow]
  congr 1
  ring

theorem disc_cocycle (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀))
    (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hZ : IsUnit Z) (hi : IsDiscMap bk.ev i) (hWZ : s.W * Z.map i = Y.map bk.iA)
    (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (Per.σA (g : GQ l)) G) :
    ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀),
      G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) =
        bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧
      bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) =
        bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) :=
  GlobalTheory.T.exists_semistable_disc_cocycle l K bk τ hτ d ρ s Y Z i hZ hi hWZ g G hG

theorem frob_eq (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} (M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (A A' : Matrix (Fin d) (Fin d) bk.S) (hA : A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S))
    (hφ : bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev))
    (hdet : (Y.map bk.iA).det ≠ 0) (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (Per.σA g) G)
    (hΦ : IsDiscMap WittVector.frobenius Φ) (w : (Ainf l)ˣ) (hw : Per.σA g (bk.ev bk.E) = bk.ev bk.E * w)
    (P : Matrix (Fin d) (Fin d) (Ainf l)) (hP : P.map WittVector.frobenius = P)
    (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
    (he : bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA)) :
    bk.iS bk.E ^ (2 * N) • e =
      (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA :=
  GlobalTheory.T.breuilKisin_disc_cocycle_frobenius_equation l K bk τ hτ d M N Y A A' hA hφ hdet g G Φ hG hΦ w hw P hP e he

theorem bounded (bk : BK K) {d : ℕ} (h : ℕ) (C B : Matrix (Fin d) (Fin d) (Ainf l))
    (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap WittVector.frobenius Φ) (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
    (he : bk.iS bk.E ^ h • e = C.map bk.iA * e.map Φ * B.map bk.iA) :
    ∃ (k : ℕ) (v : Matrix (Fin d) (Fin d) (Ainf l)), v.map bk.iA = (l : bk.DA bk.ρ₀) ^ k • e := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hφX : WittVector.frobenius (bk.ev X) = bk.ev X ^ l := by rw [← bk.ev_frob, frobS_X, map_pow]
  have hj : ∀ j : Fin d × Fin d, HasSum (fun x : Fin d × Fin d => Φ (e x.1 x.2) * bk.iA (C j.1 x.1 * B x.2 j.2))
      (bk.iS bk.E ^ h * e j.1 j.2) := by
    intro j
    convert hasSum_fintype _ using 1
    have := congrFun (congrFun he j.1) j.2
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply] at this
    rw [this, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul]; ring
  obtain ⟨k, v, hv, -⟩ := GlobalTheory.BSP.exists_bounded_of_phi_equation l K bk (Ainf l) bk.ev ι tb WittVector.frobenius hφX
    Φ hΦ (Fin d × Fin d) (fun x j => C j.1 x.1 * B x.2 j.2) (fun _ _ => Set.toFinite _) h
    (fun x => e x.1 x.2) (by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot) hj
  refine ⟨k, Matrix.of fun a b => v (a, b), ?_⟩
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact hv (a, b)

theorem descend (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} (M k : ℕ) (Y v : Matrix (Fin d) (Fin d) (Ainf l))
    (T : Matrix (Fin d) (Fin d) (WCb l)) (hT : IsUnit T) (hY : Y.map (inclW l) = inclW l τ ^ M • T) (g : GQ l)
    (P : Matrix (Fin d) (Fin d) ℤ_[l])
    (hv : Per.σA g τ ^ M • (Y * v) =
      (l : Ainf l) ^ k • τ ^ M • (P.map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA g))) :
    ∃ a : Matrix (Fin d) (Fin d) (Ainf l), P.map (algebraMap ℤ_[l] (WCb l)) * T.map (galW l g) = T * a.map (inclW l) ∧
      (l : Ainf l) ^ k • a = v := by
  have hτu := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hTd : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  set P' := P.map (algebraMap ℤ_[l] (WCb l)) with hP'
  have hPA : (P.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = P' := by
    exact Matrix.ext fun i j => (inclWA l).commutes (P i j)
  have hgY : (Y.map (Per.σA g)).map (inclW l) = inclW l (Per.σA g τ) ^ M • T.map (galW l g) := by
    have : (Y.map (Per.σA g)).map (inclW l) = (Y.map (inclW l)).map (galW l g) := by
      ext i j; simp only [Matrix.map_apply, galW_inclW]
    rw [this, hY]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, galW_inclW]
  have hW := congrArg (fun M => M.map (inclW l)) hv
  beta_reduce at hW
  rw [map_smul_hom, map_smul_hom, map_smul_hom, Matrix.map_mul, Matrix.map_mul, hY, hPA, hgY, map_pow, map_pow, map_pow,
    map_natCast] at hW
  have hu : IsUnit (inclW l (Per.σA g τ) ^ M * inclW l τ ^ M) := ((hτu.2.2.2 g).pow M).mul (hτu.1.pow M)
  have hW2 : T * v.map (inclW l) = T * ((l : WCb l) ^ k • (T⁻¹ * (P' * T.map (galW l g)))) := by
    apply smul_cancel_of_isUnit hu
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun hW i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, Matrix.mul_smul] at this ⊢
    linear_combination this
  have hW3 : v.map (inclW l) = (l : WCb l) ^ k • (T⁻¹ * (P' * T.map (galW l g))) := by
    have := congrArg (fun M => T⁻¹ * M) hW2
    beta_reduce at this
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul, Matrix.one_mul] at this
  have hx : ∀ i j, ∃ a : Ainf l, (T⁻¹ * (P' * T.map (galW l g))) i j = inclW l (1 * a) ∧ (l : Ainf l) ^ k * a = v i j := by
    intro i j
    have hij : (l : WCb l) ^ k * (T⁻¹ * (P' * T.map (galW l g))) i j = inclW l (v i j) := by
      have := congrFun (congrFun hW3 i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this.symm
    obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by rw [map_one]; exact isUnit_one) k _
      (fun n => ⟨v i j, by rw [hij, one_mul, sub_self]; exact dvd_zero _⟩)
    refine ⟨a, ha, inclW_injective ?_⟩
    rw [map_mul, map_pow, map_natCast, ← hij, ha, one_mul]
  choose a ha1 ha2 using hx
  refine ⟨Matrix.of a, ?_, ?_⟩
  · have : (Matrix.of a).map (inclW l) = T⁻¹ * (P' * T.map (galW l g)) := by
      exact Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.of_apply, ha1, one_mul]
    rw [this, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
  · exact Matrix.ext fun i j => by simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ha2]

theorem galois_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA) → ∃ F₀ : Frame bk N d ρ, F₀.toPre = F ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → IsDiscMap bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F₀.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
  intro l _ K bk τ hτ d ρ hρ s N F Y Z hY hZ hWZ
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨hmaps, hgal, -, hρ0, hρ1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  have hinj : Function.Injective bk.iA :=
    (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ hρ0 hρ1).1
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ hρ0 hρ1).1
  obtain ⟨i₀, hi₀⟩ := hmaps bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Φ, hΦ⟩ := hmaps (Ainf l) (Ainf l) WittVector.frobenius (bk.ev X) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0
    (by rw [pow_one, ← bk.ev_frob, frobS_X, map_pow]; exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero) (by rw [pow_one])
  have hτu := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hYφ := frob_Y bk hτ F s.N Y hY
  have hdet : (Y.map bk.iA).det ≠ 0 := by
    rw [← hWZ i₀ hi₀, Matrix.det_mul]
    refine mul_ne_zero (det_ne_zero_of_mul_eq_smul (pow_ne_zero _ hτu.2.1) s.W_mul) ?_
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hZ.map (RingHom.mapMatrix i₀))).ne_zero
  have key : ∀ g : ↥(GK K), ∃ a : Matrix (Fin d) (Fin d) (Ainf l),
      zW (ρ g) * F.T.map (galW l (g : GQ l)) = F.T * a.map (inclW l) ∧
      ∀ (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G →
        IsDiscMap bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * a.map bk.iA) =
          bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
    intro g
    obtain ⟨G, hG⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
    obtain ⟨e, heA, heD⟩ := disc_cocycle bk hτ s Y Z i₀ hZ hi₀ (hWZ i₀ hi₀) g G hG
    obtain ⟨w, hw⟩ := gal_E bk (g : GQ l)
    have hP : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map WittVector.frobenius =
        (ρ g).map (algebraMap ℤ_[l] (Ainf l)) := by
      ext i j; simp only [Matrix.map_apply, frob_zl]
    have hφe := frob_eq bk hτ s.N N Y F.A F.A' F.A_mul hYφ hdet (g : GQ l) G Φ hG hΦ w hw _ hP e heD
    obtain ⟨k, v, hv⟩ := bounded bk (2 * N) _ _ Φ hΦ e hφe
    have hvA : Per.σA (g : GQ l) τ ^ s.N • (Y * v) = (l : Ainf l) ^ k • τ ^ s.N •
        ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) := by
      apply Matrix.map_injective hinj
      beta_reduce
      simp only [map_smul_hom, Matrix.map_mul, hv, map_pow, map_natCast]
      rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, heD, smul_comm]
    obtain ⟨a, ha1, ha2⟩ := descend bk hτ s.N k Y v F.T F.unit hY (g : GQ l) (ρ g) hvA
    have hae : a.map bk.iA = e := by
      refine smul_cancel_of_isUnit ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k) ?_
      rw [← hv, ← ha2, map_smul_hom, map_pow, map_natCast]
    refine ⟨a, ha1, fun G' i hG' hi => ?_⟩
    rw [hG'.unique hG, hi.unique hi₀, hae]
    exact heA
  choose ε hε using key
  exact ⟨{ F with ε := ε, gal := fun g => (hε g).1 }, rfl, fun g G i hG hi => (hε g).2 G i hG hi⟩

end GlobalTheory.BKLim.GalStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTypeOfExtensionLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_type_of_extension_lattice : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL) (Sig : Finset (ZMod e)), (0 : ZMod e) ∈ Sig → TameType a ϖ Pl T Sig → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → TameType a ϖ Pl (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) Sig := by
  first | exact @GlobalTheory.TameExt.tameType_extLat | exact GlobalTheory.TameExt.tameType_extLat | (intros; apply GlobalTheory.TameExt.tameType_extLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundSeq

theorem tensor_fundamental_sequence :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V], (∀ (u : V ⊗[ℚ_[l]] P.R.B) (w : V ⊗[ℚ_[l]] P.R.BdR), ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := LL) (V := V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := V) x = u ∧ ιV (P.PD K) (LL := LL) (V := V) x - y = w) ∧ ∀ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL := LL) (V := V) x = x → ιV (P.PD K) (LL := LL) (V := V) x ∈ FilV (P.PD K) (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
  intro l _ P AI hT K LL _ _ V _ _ _ _
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT
  have hA : ∀ u : V ⊗[ℚ_[l]] P.R.B, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      x - φVB (P.PD K) (LL := LL) (V := V) x = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx⟩ := h1 b
      refine ⟨v ⊗ₜ x, ?_⟩
      have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
      rw [this, P.PD_φ, ← TensorProduct.tmul_sub, hx]
    | add u u' hu hu' =>
      obtain ⟨x, hx⟩ := hu
      obtain ⟨x', hx'⟩ := hu'
      refine ⟨x + x', ?_⟩
      rw [map_add, ← hx, ← hx']
      abel
  have hB : ∀ w : V ⊗[ℚ_[l]] P.R.BdR, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      φVB (P.PD K) (LL := LL) (V := V) x = x ∧
        ιV (P.PD K) (LL := LL) (V := V) x - w ∈ FilV (P.PD K) (LL := LL) (V := V) 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx, hx'⟩ := h2 K b
      refine ⟨v ⊗ₜ x, ?_, ?_⟩
      · have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
        rw [this, P.PD_φ, hx]
      · have : ιV (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).ι x := rfl
        rw [this, P.PD_ι, ← TensorProduct.tmul_sub]
        exact ⟨v ⊗ₜ ⟨P.ιB x - b, hx'⟩, rfl⟩
    | add w w' hw hw' =>
      obtain ⟨x, hx, hy⟩ := hw
      obtain ⟨x', hx', hy'⟩ := hw'
      refine ⟨x + x', by rw [map_add, hx, hx'], ?_⟩
      have := Submodule.add_mem _ hy hy'
      rw [map_add]
      convert this using 1
      abel
  refine ⟨fun u w => ?_, fun x hx hF =>
    GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero (P.PD K) x hx hF⟩
  obtain ⟨x₀, hx₀⟩ := hA u
  obtain ⟨x₁, hx₁, hy⟩ := hB (w - ιV (P.PD K) (LL := LL) (V := V) x₀)
  refine ⟨x₀ + x₁, _, hy, ?_, ?_⟩
  · rw [map_add, hx₁, ← hx₀]
    abel
  · rw [map_add]
    abel

end GlobalTheory.FundSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypothesesStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremB_of_localFilteredHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap := by
  first | exact @GlobalTheory.theoremB_of_admitted_inputs | exact GlobalTheory.theoremB_of_admitted_inputs | (intros; apply GlobalTheory.theoremB_of_admitted_inputs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionEqTwistedCoefficientsCocycleIff
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory

theorem actTw_eq_twCoef_and_isCoc_iff : ∀ {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]
    (χ : G →* Oˣ),
    (∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m) ∧
    ∀ z : G → ↥L.T ⊗[O] X, tableLineDegreeTwo.IsCoc L X χ z ↔ z ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  intro G _ _ LL _ O _ _ V _ _ _ _ ρ L X _ _ χ
  have h1 : ∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul]
      rw [coefRep_tmul, twistRep_apply]
      simp [latRep, smul_tmul', MonoidHom.inv_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  refine ⟨h1, fun z => ?_⟩
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨⟨hz, fun _ => Submodule.mem_top⟩, ?_⟩
    show (ReciprocityTheory.Def.d1 (twCoef (latRep L) χ X)) z = 0
    funext x
    change twCoef (latRep L) χ X x.1 (z x.2) - z (x.1 * x.2) + z x.1 = 0
    rw [hc, ← h1]; abel
  · rintro ⟨⟨hz, -⟩, hk⟩
    refine ⟨hz, fun g h => ?_⟩
    have e : twCoef (latRep L) χ X g (z h) - z (g * h) + z g = 0 := congrFun hk (g, h)
    rw [h1, ← sub_eq_zero, ← neg_eq_zero, ← e]; abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtens
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

namespace GlobalTheory.PotDirect

theorem main : StepPotDirect := by
  intro D P hT hFo h0 hBr hPH hChi hIE h12 hTen hTP i k hl r ρ hr π hπ hdec Xs hπX hTL w hw
  obtain ⟨Y, u, hu, hY, hYc, hX, hχ, hχσ⟩ := GlobalTheory.TypeInertia.inertial_chars D P hT h0 hPH hChi i k hl r hr Xs hTL w hw
  have hχc : Continuous fun g => ((chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have hab : a = b := Subsingleton.elim a b
    subst hab
    simpa [chiGL, Matrix.scalar] using D.nd.chi_cont i 1
  obtain ⟨K', h, hN, hF', hS, hpc, hpc0, hker⟩ := GlobalTheory.PotExt.main D P h12 i k w hw Y (fun y hy => (hY y hy).1) (↥Xs) D.R.nV
    (fun x => r x) 1 (chiGL i) (fun x => (hr x).1) hχc (fun x => (hX x x.2).1) hχ
  obtain ⟨ch, hch⟩ := GlobalTheory.InertiaChars.main D P hTP hIE i k hl w hw Y hY K' h hN hF' hS hker
  have hdeg := (GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw
  refine GlobalTheory.T.twistedFamily_potentiallyCrystalline_frobStable D hTen i w hw hdeg r Xs K' h hN hF' hS (Y.image ch) (ch u) (D.R.nV + 1)
    (Finset.mem_image_of_mem _ hu) (Finset.card_image_le.trans hYc) (fun x _ => (hr x).1) ?_ hpc0 ?_
  · intro x hx
    obtain ⟨M, hM, hσ⟩ := (hX x hx).2
    exact ⟨hpc ⟨x, hx⟩, hch Y subset_rfl _ (r x) (hr x).1 (hpc ⟨x, hx⟩) M hM hσ⟩
  · have := hch {u} (by simpa using hu) 1 (chiGL i) hχc hpc0 {u} (by simp) (fun σ hσ => by simpa using hχσ σ hσ)
    simpa using this

end GlobalTheory.PotDirect
end

