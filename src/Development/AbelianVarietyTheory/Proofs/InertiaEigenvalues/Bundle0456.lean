import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitLiftOfLiftParam
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeInduction
section
namespace GlobalTheory.BaseChangeInduction

theorem baseChange_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : GlobalTheory.Prism.SemiBC u)
    (p : N → Prop) (hzero : p 0) (hadd : ∀ y z, p y → p z → p (y + z))
    (hsmul : ∀ (r : B) (y : N), p y → p (r • y)) (himg : ∀ x : M, p (u x)) (y : N) : p y := by
  let S : Submodule B N :=
    { carrier := {n | p n}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      smul_mem' := fun r n hn => hsmul r n hn }
  have hq : S.mkQ = 0 := by
    refine (h (N ⧸ S) 0).unique (fun x => ?_) (fun x => rfl)
    exact (Submodule.Quotient.mk_eq_zero S).2 (himg x)
  have hy : S.mkQ y = 0 := by rw [hq]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 hy

end GlobalTheory.BaseChangeInduction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcPartsTempered
section
noncomputable section

namespace GlobalTheory.RowCuspPar

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

variable (D : D7)

def blockPart (μ : D.naut.CG 1) : Part D.naut.CG := ⟨1, μ, D.R.t⟩

def liftLoc (μ : D.naut.CG 1) (w : PlE D.host) (a : D.naut.LP w) : D.naut.LP w :=
  D.naut.lpChar (D.naut.lpSum a (spehLoc D.nd D.naut (blockPart D μ) w)) (D.naut.locG D.naut.etaTinv w)

def eOf {R : Ranks} (P : HCParam R) (j : ℕ) : ℚ := if h : j - 1 < R.m then P.e ⟨j - 1, h⟩ else 0

def runE (R : Ranks) (e : ℚ) : Multiset ℂ :=
  (Multiset.range R.t).map fun k : ℕ => -(e : ℂ) + ((R.t : ℂ) - 1) / 2 - (k : ℂ)

def IsThetaLift (S : GlobalTheory.HeightCounting.RowSide D) (μ : D.naut.CG 1) (j : ℕ) (σ : D.what₂.FT) (P : D.nbc.AU j) : Prop :=
  (∀ w, IsSplitPl D.host w → D.nbc.locAU j P w = liftLoc D μ w (S.locR σ w)) ∧
  (∀ w, ¬ IsSplitPl D.host w → D.nbc.sphAU j P w) ∧
  ∀ τ : D.what₂.Tau,
    D.nbc.infW j (D.nbc.wtAU j P) (embTau D τ) =
        (hcSigma (D.hc τ) + runE D.R (eOf (D.hc τ) j)).map (fun z => z - 1 / 2) ∧
    D.nbc.infW j (D.nbc.wtAU j P) (embTauBar D τ) =
        (hcSigma (D.hc τ) + runE D.R (eOf (D.hc τ) j)).map (fun z => -(z - 1 / 2))

def ThetaLiftRow (S : GlobalTheory.HeightCounting.RowSide D) (μ : ℕ → D.naut.CG 1) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → ∃ P : D.nbc.AU j, IsThetaLift D S (μ j) j σ P

def IsBCU (j : ℕ) (P : D.nbc.AU j) (Pa : List (Part D.naut.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
  rankIso D.nd D.naut Pa = D.R.nV ∧
  (∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Pa w = D.nbc.locAU j P w) ∧
  (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (isoLoc D.nd D.naut Pa w) ∧
    D.naut.frobEig (isoLoc D.nd D.naut Pa w) = ubc D.R.nV (D.nbc.satAU j P w)) ∧
  ∀ τ, isoInf D.nd D.naut Pa τ = D.nbc.infW j (D.nbc.wtAU j P) τ

def BaseChangeU : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ P : D.nbc.AU j, (∀ w, ¬ IsSplitPl D.host w → D.nbc.sphAU j P w) →
    ∃ Pa, IsBCU D j P Pa

def BcPartsTempered : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ (P : D.nbc.AU j) (Pa : List (Part D.naut.CG)), IsBCU D j P Pa →
    ∀ p ∈ Pa, ∀ w, IsSplitPl D.host w → D.naut.unr (D.naut.locG p.π w) → D.naut.tempered (D.naut.locG p.π w)

def RowSizeR (S : GlobalTheory.HeightCounting.RowSide D) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
    D.naut.unr (S.locR σ w) → ∀ α ∈ D.naut.frobEig (S.locR σ w),
      ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)

def RowUnrR (S : GlobalTheory.HeightCounting.RowSide D) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
    (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (S.locR σ w)

def CharFacts (μ : ℕ → D.naut.CG 1) : Prop :=
  D.naut.csd D.naut.etaT ∧
  (∀ j τ, D.naut.infG (μ j) (embTau D τ) = {-((eOf (D.hc τ) j : ℚ) : ℂ)} ∧
    D.naut.infG (μ j) (embTauBar D τ) = {((eOf (D.hc τ) j : ℚ) : ℂ)}) ∧
  (∀ τ, D.naut.infG D.naut.etaT (embTau D τ) = {1 / 2} ∧ D.naut.infG D.naut.etaT (embTauBar D τ) = {-1 / 2} ∧
    D.naut.infG D.naut.etaTinv (embTau D τ) = {-1 / 2} ∧ D.naut.infG D.naut.etaTinv (embTauBar D τ) = {1 / 2}) ∧
  (∀ j w, IsSplitPl D.host w → D.naut.unr (D.naut.locG (μ j) w) → D.naut.tempered (D.naut.locG (μ j) w)) ∧
  (∀ w, IsSplitPl D.host w → D.naut.tempered (D.naut.locG D.naut.etaTinv w)) ∧
  ∀ w (a : D.naut.LP w), D.naut.lpChar (D.naut.lpChar a (D.naut.locG D.naut.etaTinv w)) (D.naut.locG D.naut.etaT w) = a

section Iso
variable {D}
open GlobalTheory.HeightCounting

theorem isoLoc_perm {Pa Pb : List (Part D.naut.CG)} (h : Pa.Perm Pb) (w : PlE D.host) :
    isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pb w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons p _ ih => simp only [List.foldr_cons, ih]
  | swap p q l =>
    simp only [List.foldr_cons]
    rw [← D.naut.lpSum_assoc, D.naut.lpSum_comm (spehLoc D.nd D.naut q w), D.naut.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem isoLoc_single (p : Part D.naut.CG) (hd : p.d = 1) (w : PlE D.host) :
    isoLoc D.nd D.naut [p] w = D.naut.locG p.π w := by
  obtain ⟨a, π, d⟩ := p
  simp only at hd
  subst hd
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

end Iso
end GlobalTheory.RowCuspPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPeriodMatrixOverAcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.CrisPeriods

variable {l : ℕ} [Fact l.Prime]

private theorem padicInt_hom_ext (f g : ℤ_[l] →+* Per.Ainf l) (z : ℤ_[l]) : f z = g z := by
  have hH : IsHausdorff (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = w * (l : ℤ_[l]) ^ n + (z.appr n : ℤ_[l]) := by rw [hw]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f w - g w, ?_⟩
  have hf := congrArg f hz
  have hg := congrArg g hz
  simp only [map_add, map_mul, map_pow, map_natCast] at hf hg
  rw [hf, hg]
  ring

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] {n : Type} (f : R →+* S) (c : R)
    (M : Matrix n n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

theorem exists_lift (C : Core l) (hA : C.AwayT) {d : ℕ} (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Z : Matrix (Fin d) (Fin d) (Per.Acris l),
      Z.map (algebraMap (Per.Acris l) (Per.Bcris l)) = algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ N • U := by
  haveI : IsLocalization.Away C.t (Per.Bcris l) := hA
  have h : ∀ i j, ∃ k : ℕ, ∃ a : Per.Acris l,
      U i j * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ k = algebraMap (Per.Acris l) (Per.Bcris l) a := by
    intro i j
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers C.t) (U i j)
    obtain ⟨k, hk⟩ := s.2
    refine ⟨k, a, ?_⟩
    have hk' : C.t ^ k = (s : Per.Acris l) := hk
    rw [← map_pow, hk']
    exact hs
  choose k a ha using h
  refine ⟨Finset.univ.sup fun p : Fin d × Fin d => k p.1 p.2, fun N hN =>
    ⟨Matrix.of fun i j => a i j * C.t ^ (N - k i j), ?_⟩⟩
  ext i j
  have hk : k i j ≤ N :=
    le_trans (Finset.le_sup (f := fun p : Fin d × Fin d => k p.1 p.2) (Finset.mem_univ (i, j))) hN
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, ← ha]
  rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hk, mul_comm]

end GlobalTheory.CrisPeriods

namespace GlobalTheory.CrisPeriods

theorem periods_over_Acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), C.t ^ N • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • Z) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  intro l _ K P AI T C _hFits bk d ρ U U' hUU' hgal c₁ F hφ
  have hA := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).1
  obtain ⟨_, _, -, -, -, hFilt, -⟩ := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
  obtain ⟨-, hmul, -, hiff, -, -, hinj⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm
  have AL := GlobalTheory.MemLoc.ActLaws.act_laws l
  obtain ⟨N₁, h₁⟩ := exists_lift C hA U
  obtain ⟨N₂, h₂⟩ := exists_lift C hA U'
  refine ⟨max N₁ N₂, fun N hN X X' hX hX' => ?_⟩
  obtain ⟨Z, hZ⟩ := h₁ N (le_of_max_le_left hN)
  obtain ⟨Z', hZ'⟩ := h₂ N (le_of_max_le_right hN)
  have hmi : Function.Injective
      (fun M : Matrix (Fin d) (Fin d) (Per.Acris l) => M.map (algebraMap (Per.Acris l) (Per.Bcris l))) :=
    Matrix.map_injective hinj
  have hXm : ∀ Y : Matrix (Fin d) (Fin d) bk.S,
      ((Y.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))).map C.ι =
        Y.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) := by
    intro Y
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply]
    rw [C.ι_j]
    congr 1
    exact (congrArg C.j (GlobalTheory.RingIface.tower l (bk.ev (Y i j)))).trans
      ((C.j_cris.on0 _).trans (congrArg _ (Subalgebra.coe_algebraMap _ _)))
  have htN : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ^ N ∈ Per.FilD l N := by
    rw [C.ι_j, ← map_pow, hiff, hFilt]
    exact Ideal.mem_span_singleton_self _
  refine ⟨Z, Z', ?_, ?_, ?_, ?_, ?_⟩
  · apply hmi
    simp only
    rw [Matrix.map_mul, hZ, hZ', map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), smul_mul_smul_comm,
      hUU', map_pow, ← pow_add, two_mul]
  · apply hmi
    simp only
    have hZφ : (Z.map (phiA l)).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.φB l) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.2 (Z i j)).symm
    have hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
      exact (GlobalTheory.RingIface.aB_eq_alg l _).symm
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (phiA l C.t) =
        Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.2 C.t).symm
    rw [map_smul_ring, hZφ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hFm, hZ, map_pow, map_pow, ht,
      Matrix.smul_mul, ← hφ]
    simp only [map_mul, map_pow, map_natCast, smul_smul]
    congr 1
    ring
  · intro g
    apply hmi
    simp only
    have hZσ : (Z.map (sigA (g : GQ l))).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.σB (g : GQ l)) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ (Z i j)).symm
    have hρ : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = (ρ g).map (Per.zB l) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply]
      rw [GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg, padicInt_hom_ext (Per.zA l) (algebraMap ℤ_[l] (Ainf l))]
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) C.t) =
        Per.σB (g : GQ l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ C.t).symm
    rw [map_smul_ring, Matrix.map_mul, hρ, hZσ, hZ, map_smul_ring, map_smul_ring, hZ]
    simp only [map_pow, ht]
    rw [Matrix.mul_smul, hgal, smul_smul, smul_smul, mul_comm]
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) =
        ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι ((U * (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l))) i j) =
        (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX i j)
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) =
        ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z').map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι (((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) * U') i j) =
        (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX' i j)

end GlobalTheory.CrisPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToOD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.CrisBounded

theorem dvd_of_ev_eq_zero {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l))
    (m : ℕ) (y : Per.BdRp l) (hy : Per.ev l m y = 0) : ainfToBdRp l d ^ m ∣ y := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have h2 := hd.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  have h3 : d ∣ GlobalTheory.MemLoc.xi e := Ideal.mem_span_singleton.1 (h2 ▸ Ideal.mem_span_singleton_self _)
  have h4 := ((GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE).1 m y).1 ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m y).2 hy)
  exact (pow_dvd_pow_of_dvd (map_dvd (GlobalTheory.MemLoc.aDp l) h3) m).trans h4

theorem bdd_crisP {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ) :
    ∃ N : ℕ, ∀ x : Per.Acris l, ∃ a : Ainf l,
      ainfToBdRp l d ^ m ∣ (l : Per.BdRp l) ^ N * acrisToBdRp l x - ainfToBdRp l a := by
  obtain ⟨N, hN⟩ := (isCrisP_crisP l).bdd m
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN x
  refine ⟨a, dvd_of_ev_eq_zero hd m _ ?_⟩
  rw [map_sub, sub_eq_zero]
  exact ha.trans (GlobalTheory.MemLoc.CrisUnique.ev_aDp m a).symm

theorem bdd_tensor {Z O A C D : Type} [CommRing Z] [CommRing O] [Algebra Z O] [Module.Free Z O]
    [Module.Finite Z O] [CommRing A] [Algebra Z A] [CommRing C] [Algebra Z C] [CommRing D] [Algebra Z D]
    (f : A →ₐ[Z] D) (j : C →ₐ[Z] D) (t : D) (n : ℕ) (h : ∀ x : C, ∃ a : A, t ∣ (n : D) * j x - f a)
    (z : O ⊗[Z] C) : ∃ y : O ⊗[Z] A, ((1 : O) ⊗ₜ[Z] t) ∣
      (n : O ⊗[Z] D) * Algebra.TensorProduct.map (AlgHom.id O O) j z -
        Algebra.TensorProduct.map (AlgHom.id O O) f y := by
  let b := Module.Free.chooseBasis Z O
  choose a c hc using fun i => h (GlobalTheory.Decompl.crd b i z)
  refine ⟨∑ i, b i ⊗ₜ[Z] a i, ∑ i, b i ⊗ₜ[Z] c i, GlobalTheory.Decompl.ext_crd b fun i => ?_⟩
  rw [map_sub, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_mul,
    GlobalTheory.Decompl.crd_sum, GlobalTheory.Decompl.crd_sum, hc]

theorem bdd_crisToOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ), ∃ N : ℕ, ∀ z : OCr l O, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ N * crisToOD l O z - toOD l O y := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m
  rw [show ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) from
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))]
  obtain ⟨N, hN⟩ := bdd_crisP (ϖ.span_ev_eis 1) m
  refine ⟨N, fun z => ?_⟩
  obtain ⟨y, hy⟩ := bdd_tensor (ainfToBdRp l) (acrisToBdRp l) _ (l ^ N)
    (fun x => by rw [Nat.cast_pow]; exact hN x) z
  refine ⟨y, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← Nat.cast_pow]
  exact hy

end GlobalTheory.BKReal.CrisBounded
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => coeff (l * n + i) z

theorem coeff_frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) (n : ℕ) :
    coeff n (frobSlice l i z) = coeff (l * n + i) z := by
  simp [frobSlice]

namespace Hom

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

def rdivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ F.mat τ * Y = h • (1 : Matrix κ κ K⟦X⟧)}

def ldivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ Y * F.mat τ = h • (1 : Matrix ι ι K⟦X⟧)}

theorem bdd_mul {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f * g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  exact ⟨a * b, fun n => by
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0 hb0
      (f := f) (g := g) (by simpa using ha) (by simpa using hb) n⟩

theorem bdd_add {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f + g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨max a b, fun n => by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha n) (hb n))⟩

theorem bdd_smul_matrix {μ ν : Type} {b : K⟦X⟧} {Y : Matrix μ ν K⟦X⟧} (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c)
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n ((b • Y) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨c, hc⟩ := hY
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  refine ⟨a * max c 0, fun i j n => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0
    (le_max_right c 0) (f := b) (g := Y i j) (by simpa using ha)
    (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _)) n

theorem rdivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (hy : y ∈ F.rdivSet τ) :
    x + y ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.mul_add, h₁, h₂, add_smul]

theorem ldivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (hy : y ∈ F.ldivSet τ) :
    x + y ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.add_mul, h₁, h₂, add_smul]

theorem rdivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.mul_smul, h, smul_smul]

theorem ldivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.smul_mul, h, smul_smul]

end Hom

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoQuotientOfDivisibleImageMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_quotient_of_divisible_image_mem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ HfD (P.PD K) LA → c ∈ HfQ (P.PD K) LA _ hI := by
  first | exact @GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD | exact GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD | (intros; apply GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoReductionsOrthogonalModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_reductions_orthogonal_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), Formalism.MainNotions.N.bkACore (P.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), ∀ c ∈ HfQ (P.PD K) LA _ hI, ∀ c' ∈ HfQ (P.PD K) LA' _ hI', CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c') := by
  first | exact @GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA | exact GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA | (intros; apply GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDetMemHeckeAlgebraOfHeckeSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem blockDet_mem : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, InRing T rep (Θ p q)) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  intro Γ X O _ _ n T rep hc g Θ hΘ
  exact GlobalTheory.BlockDet.main T n (ringR T rep)
    (fun m a ha d => GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T rep hc m a (fun k => (mem_ringR T rep _).1 (ha k)) d)
    g Θ (fun p q => (mem_ringR T rep _).2 (hΘ p q))

end GlobalTheory.SpanRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphismStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T T' : Lat a O K ϖ) (I : Ident t ϖ P T) (I' : Ident t ϖ Q T'), IsBK I → IsBK I' → ∀ f : LatHom T.L T'.L, ∃ F, IsMapOf I I' f F := by
  first | exact @GlobalTheory.BKReal.Full.main | exact GlobalTheory.BKReal.Full.main | (intros; apply GlobalTheory.BKReal.Full.main <;> assumption)
end

