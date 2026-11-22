import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.Per.CharJumps

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_act (g : G) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g w) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, AlgebraTensorModule.map_tmul, PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ιV_mem_DdR {w : V ⊗[Qp] B} (hw : w ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) w ∈ DdR PD ρ := by
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hw ⊢
  intro g
  rw [← ιV_act, hw g]

theorem ιV_mul (a : K₀) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (B := B) (V := V) (LL := LL) a w) =
      mulVdR (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K a) (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, mulVB, mulVdR, AlgebraTensorModule.map_tmul, ← IsScalarTower.algebraMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem ιV_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {w : V ⊗[Qp] B} (hw : w ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) w ∈ DdRE PD ρ τ := by
  unfold DcrisL at hw
  unfold DdRE
  rw [Submodule.mem_inf] at hw ⊢
  refine ⟨ιV_mem_DdR PD ρ hw.1, ?_⟩
  have h2 := hw.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  obtain ⟨a, rfl⟩ := hs c
  rw [← ιV_mul, h2 a, map_smul]
  simp

theorem FilV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v s =>
    exact ⟨v ⊗ₜ ⟨(s : BdR), PD.Fil_anti a s.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem FilV_anti : Antitone fun a : ℤ => FilV PD (LL := LL) (V := V) a :=
  antitone_int_of_succ_le (FilV_succ_le PD)

end General

end GlobalTheory.Per.CharJumps

namespace GlobalTheory.Per.CharJumps

theorem inf_of_line {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M] (D : Submodule LL M)
    (hD : finrank LL ↥D = 1) (F : ℤ → Submodule LL M) (hF : Antitone F) {x : M} (hx : x ∈ D)
    (d : ℤ) (h1 : x ∈ F d) (h2 : x ∉ F (d + 1)) (b : ℤ) :
    D ⊓ F b = if b ≤ d then D else ⊥ := by
  have hx0 : x ≠ 0 := fun h => h2 (h ▸ (F (d + 1)).zero_mem)
  have hspan : ∀ y ∈ D, ∃ c : LL, c • x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : ↥D)
      (fun h => hx0 (congrArg Subtype.val h))).1 hD ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  split_ifs with hb
  · refine inf_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := hspan y hy
    exact (F b).smul_mem c (hF hb h1)
  · rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨c, rfl⟩ := hspan _ hy.1
    rw [Submodule.mem_bot]
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply h2
      have hxe : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hxe]
      exact hF (by omega) ((F b).smul_mem _ hy.2)

theorem jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  intro l _ P AI T K LL hA μ hμ d hw hcrys τ b
  haveI := LL.2
  haveI := K.2
  have hdr : IsDR (P.PD K) (charRep μ) := by
    let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      { V := ↥LL.1, ρ := charRep μ,
        cont := fun x => by
          show Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id x
          exact hμ.smul continuous_const }
    exact ((GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI T K) ↥LL.1 ↥(OL LL)
      (GlobalTheory.LocalIntegers.good_integers l LL).1 A).2.2 hcrys
  obtain ⟨-, -, hdim⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)).1 τ
  have h1 : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdim hdr, Module.finrank_self]
  have hs : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun c => ⟨⟨c.1, c.2, hA.1 c.2⟩, rfl⟩
  obtain ⟨w, hwD, hin, hout⟩ := hw τ
  have hx := ιV_mem_DdRE (P.PD K) (charRep μ) hs τ hwD
  have key := inf_of_line _ h1 _ (FilV_anti (P.PD K)) hx (d τ) hin hout
  have fk : ∀ c : ℤ, (finrank ↥LL.1 ↥(FildR (P.PD K) (charRep μ) τ c) : ℤ) = if c ≤ d τ then 1 else 0 := by
    intro c
    unfold FildR
    rw [key c]
    by_cases hc : c ≤ d τ
    · rw [if_pos hc, if_pos hc, h1]
      rfl
    · rw [if_neg hc, if_neg hc, finrank_bot]
      rfl
  unfold multV
  rw [fk b, fk (b + 1)]
  split_ifs <;> omega

end GlobalTheory.Per.CharJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsFrobeniusEqMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discPeriods_map_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ → ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ = s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  first | exact @GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul | exact GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul | (intros; apply GlobalTheory.BSP.Seed.crystallineDiscPeriods_frobenius_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEqStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineDiscPeriods_galois_action_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (Per.σA (g : GQ l)) G → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ x, G (j x) = j x) ∧ bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) = G (bk.iA τ) ^ s.N • s.W := by
  first | exact @GlobalTheory.BSP.seed_gal_periods | exact GlobalTheory.BSP.seed_gal_periods | (intros; apply GlobalTheory.BSP.seed_gal_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePotentialFamily
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDualU

theorem dualLatLe_of {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] [IsDomain O] [IsFractionRing O LL]
    (U U' : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL)
    (LT' : Lattice (O := O) U'.ρ) (hLT' : IsDualLat1 PD LT LT' P) (hopen : IsOpen (LT'.T : Set U'.V)) (b : ℕ)
    (h : finrank LL (FiniteCohomology PD U'.ρ) + finrank O ↥LT.T ≤ b) : DualLatLe PD U U' LT P b :=
  ⟨LT', hLT', by rw [GlobalTheory.TopSteps.FinSummand.finrank_h1fT PD LT' hopen]; exact h⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → admBK (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ n : ℕ,
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsDR (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1).ρ ∧
      ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PU : (locU i w hw M hSub.1).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) U' ∧
        DualLatLe (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1) U' (Br.locLat D.nbr i w hw M) PU (2 * k) := by
  intro D hF hDR hBK i r hR Xs w hw hK n hPot k M hSub
  have hSum := GlobalTheory.T.isComplementedSubrep_localMatrixRep_twistedSum D i r hR Xs w hw k M hSub
  obtain ⟨hU, X', PX, hD1, hSF⟩ := GlobalTheory.T.potential_family_summand_restriction D hF hDR i r hR Xs w hw n hPot _ hSum
  have hX' := GlobalTheory.T.tateDual_twistedSumSummand_isDeRham D hF hDR i r hR Xs w hw n hPot _ hSum X' PX hD1
  have hGood := goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL
  have hcyc : ∀ g, ∃ u : (Br.OLL D.nbr i w hw)ˣ, ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g :
      (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) (u : Br.OLL D.nbr i w hw) := by
    intro g
    rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
    exact ⟨Units.map (D.nbr i w hw).eO.toRingHom.toMonoidHom (epsU D.nd i ((decS D.nd w) (Br.iota D.nbr i w hw g))), rfl⟩
  obtain ⟨LT', hLT', hopen⟩ := GlobalTheory.T.exists_dualLattice_isOpen_perfectPairing (Br.PD D.loc D.nbr i w hw) hGood hcyc _ X' PX hD1
    (Br.locLat D.nbr i w hw M)
  refine ⟨hU, X', PX, hSF, ?_⟩
  obtain ⟨⟨hdom, -, hfr⟩, -⟩ := hGood
  haveI := hdom
  haveI := hfr
  haveI : CompactSpace (Br.G D.nbr i w hw) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK _
  refine dualLatLe_of _ _ X' _ PX LT' hLT' hopen _ ?_
  have h2 := GlobalTheory.Pass.RankDeRham.finrank_H1f_le (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).LL hK
    (hBK (D.nd.l i) (D.nbr i w hw).Kw) X' hX'
  have h3 : finrank (Br.LL D.nbr i w hw) X'.V = k := by
    rw [← hD1.2.2.2]
    exact Module.finrank_fin_fun _
  have h4 : finrank (Br.OLL D.nbr i w hw) ↥(Br.locLat D.nbr i w hw M).T = k := by
    have e := LinearEquiv.ofInjective _ (stdG_inj (O := Br.OLL D.nbr i w hw) (LL := Br.LL D.nbr i w hw) Subtype.val_injective k)
    exact (LinearEquiv.finrank_eq e).symm.trans (Module.finrank_fin_fun _)
  have h5 : finrank (Br.LL D.nbr i w hw) (FiniteCohomology (Br.PD D.loc D.nbr i w hw) X'.ρ) ≤ k := h3 ▸ h2
  exact le_trans (Nat.add_le_add h5 h4.le) (by omega)

end GlobalTheory.Pass.LocDualU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.ResFinite

theorem adm12_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  intro D l _ K K' hKK hle LL T hc
  have hT := D.locT l
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K' LL T.V T.ρ hc).1
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (D.loc l) (D.locA l) hT K' K LL hKK T.V T.ρ).1 hc
  · intro τ a
    exact GlobalTheory.T.hodgeJumpMultiplicity_restrict_finite_ext l (D.loc l) (D.locA l) hT K' K LL hKK T.V T.ρ hdr τ a

end GlobalTheory.Per.ResFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystalline
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.ZVal

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem zval : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  intro D HW F l _ K s LL h T hT c b lam hlc hl1 hZk g₁ hg₁ z₁ hz₁ hZ₁
  have hc := GlobalTheory.HerrClassMaps.compact_GK K
  have hcl : IsClosed (((HW l).W K s LL h).GKs : Set ↥(GK K)) :=
    (lam_exists D HW K s LL h).elim fun _ hx => hx.2.2.2.2
  have hcs : CompactSpace ↥((HW l).W K s LL h).GKs := isCompact_iff_compactSpace.1 hcl.isCompact
  refine (GlobalTheory.T.exists_weakTopology_wachImage_isClosed D HW F l K s LL h T hT).elim fun τ hτ => ?_
  letI := τ
  haveI hT2 : T2Space (TW (RW LL) T) := hτ.1
  have hTG : IsTopologicalAddGroup (TW (RW LL) T) := hτ.2.1
  have hact := hτ.2.2.1
  have hemb := hτ.2.2.2.1
  have hclo := hτ.2.2.2.2
  let a : ↥((HW l).W K s LL h).GKs → TW (RW LL) T →+ TW (RW LL) T := fun g =>
    (TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K))).toAddMonoidHom
  have ha1 : ∀ g x, a g x = TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K)) x :=
    fun g x => rfl
  have hamul : ∀ g g' x, a (g * g') x = a g (a g' x) := by
    intro g g' x
    simp only [ha1]
    exact GlobalTheory.HerrClassMaps.TWact_mul _ _ _
      (fun r => GlobalTheory.HerrClassMaps.gRW_mul (D.locA l) LL _ _ r) T _ _ x
  have ha1t : ∀ g (t : ↥T.L.T), a g ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) =
      (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨T.ρ (g : ↥(GK K)) t, T.L.stable _ t t.2⟩ : ↥T.L.T) := fun g t =>
    GlobalTheory.HerrClassMaps.TWact_one_tmul _ T _ t
  have haj : ∀ g (w : ((HW l).W K s LL h).DD T), a g (((F l).E K s LL h).tie.jD T w) =
      ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ (g : ↥(GK K))) w) :=
    fun g w => (((F l).E K s LL h).tie.jD_act T (g : ↥(GK K)) w).symm
  let J : AddSubgroup (TW (RW LL) T) :=
    (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X).toAddSubgroup.map (((F l).E K s LL h).tie.jD T).toAddMonoidHom
  have hJm : ∀ x, x ∈ J ↔ ∃ w ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X,
      ((F l).E K s LL h).tie.jD T w = x := fun x => AddSubgroup.mem_map
  have hJ : IsClosed (J : Set (TW (RW LL) T)) := by
    have : (J : Set (TW (RW LL) T)) = ((F l).E K s LL h).tie.jD T ''
        (aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X : Set (((HW l).W K s LL h).DD T)) := by
      ext x
      exact (hJm x).trans Iff.rfl
    rw [this]; exact hclo
  have hJa : ∀ g, ∀ x ∈ J, a g x ∈ J := by
    intro g x hx
    refine ((hJm x).1 hx).elim fun w hw => ?_
    rw [← hw.2, haj]
    exact (hJm _).2 ⟨_, GlobalTheory.NL.XStab.xstab D HW l K s LL h T _ w hw.1, rfl⟩
  have hJk : ∀ h' : ↥((HW l).W K s LL h).GKs, lam h' = 1 → ∀ x ∈ J, a h' x = x := by
    intro h' hh x hx
    refine ((hJm x).1 hx).elim fun w hw => ?_
    rw [← hw.2, haj, hl1 h' hh, ((HW l).W K s LL h).γD_one]
  haveI hCA : ContinuousAdd (TW (RW LL) T) := hTG.toContinuousAdd
  haveI hCN : ContinuousNeg (TW (RW LL) T) := hTG.toContinuousNeg
  haveI hCS : ContinuousSub (TW (RW LL) T) :=
    ⟨Continuous.congr (continuous_fst.add continuous_snd.neg) (fun p => (sub_eq_add_neg p.1 p.2).symm)⟩
  have hZc : Continuous (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b) := by
    unfold Zf
    exact (hemb.comp (c.2.1.1.subtype_mk fun g => GlobalTheory.HerrClassMaps.mem_T c g)).add
      (((hact b).comp continuous_subtype_val).sub continuous_const)
  have hZm : ∀ g g', Zf (D.locA l) T ((HW l).W K s LL h).GKs c b (g * g') =
      Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g + a g (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g') := by
    intro g g'
    have e : (⟨(c : ↥((HW l).W K s LL h).GKs → T.V) (g * g'), GlobalTheory.HerrClassMaps.mem_T c (g * g')⟩ : ↥T.L.T) =
        ⟨(c : ↥((HW l).W K s LL h).GKs → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ +
          ⟨T.ρ (g : ↥(GK K)) ((c : ↥((HW l).W K s LL h).GKs → T.V) g'), T.L.stable _ _ (GlobalTheory.HerrClassMaps.mem_T c g')⟩ :=
      Subtype.ext (c.2.1.2 g g')
    have hz : ∀ g'', Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g'' =
        (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨(c : ↥((HW l).W K s LL h).GKs → T.V) g'', GlobalTheory.HerrClassMaps.mem_T c g''⟩ : ↥T.L.T) +
          (a g'' b - b) := fun _ => rfl
    simp only [hz, map_add, map_sub, ha1t, hamul, e, TensorProduct.tmul_add]
    abel
  have hZk' : ∀ h' : ↥((HW l).W K s LL h).GKs, lam h' = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b h' = 0 :=
    fun h' hh => hZk h' (hl1 h' hh)
  have hzJ : ((F l).E K s LL h).tie.jD T z₁ ∈ J := (hJm _).2 ⟨z₁, hz₁, rfl⟩
  have HM := (GlobalTheory.NL.ZgAll.mem_and_comm a lam hlc g₁ hg₁ J hJ hJa hJk _ hzJ
    (Zf (D.locA l) T ((HW l).W K s LL h).GKs c b) hZc hZm hZk' hZ₁).1
  intro g
  exact ((hJm _).1 (HM g)).elim fun w hw => ⟨w, hw.1, hw.2.symm⟩

end GlobalTheory.NL.ZVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrankStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamComponents_crystallineLetters_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (∀ τ, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ≤ finrank ↥LL.1 V ∧ (IsDR (P.PD K) ρ → finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V)) ∧ ∀ τ, IsCrys (P.PD K) ρ → finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = finrank ↥LL.1 V := by
  first | exact @GlobalTheory.Per.Components.components_finrank | exact GlobalTheory.Per.Components.components_finrank | (intros; apply GlobalTheory.Per.Components.components_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasis
section
noncomputable section

namespace GlobalTheory.HTBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

set_option maxHeartbeats 4000000 in

theorem exists_dR_frame : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1),
    Module.finrank ↥LL.1 ↥(DdR (P.PD K) (repOf r')) = Module.finrank ℚ_[l] ↥K.1 * m →
    ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) →
    ∃ (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ),
      (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) (repOf r') τ' a) ∧
      (∀ i j, u i j ∈ (P.PD K).Fil (k i)) ∧
      (∀ g : ↥(GK K), (∀ x ∈ LL.1, (g : GQ l) x = x) → ∀ i,
        ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
          (fun j => P.actQdR (g : GQ l) (u i j)) = u i) ∧
      (∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
        ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i) ∧
      LinearIndependent P.R.BdR u := by
  intro l _ P AI T K LL m r' hdR τ' hτ
  haveI := K.2
  haveI := LL.2
  have hDR : IsDR (P.PD K) (repOf r') := by
    unfold IsDR
    rw [hdR, Module.finrank_fin_fun]
  haveI hfinD : FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) (repOf r')) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · haveI : Subsingleton ((Fin 0 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) := ⟨fun x y => by
        have h : ∀ z : (Fin 0 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR, z = 0 := fun z => by
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add a b ha hb => rw [ha, hb, add_zero]
        rw [h x, h y]⟩
      infer_instance
    · exact Module.finite_of_finrank_pos (by rw [hdR]; exact Nat.mul_pos Module.finrank_pos hm)
  obtain ⟨m', d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) (repOf r')
    (GlobalTheory.DRFil.filSpans T K LL (repOf r') hDR) τ'
  let u' : Fin m' → Fin m → P.R.BdR := fun i => coordF P LL m (d i)
  have hspan' : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m' → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u' i := by
    intro n y hy
    have hY : (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j) ∈
        FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n :=
      Submodule.sum_mem _ fun j _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (hy j)
    have hcY : coordF P LL m (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j) = y := by
      funext j'
      simp [map_sum, Finset.sum_apply, Pi.single_apply]
    obtain ⟨r, hr, he⟩ := had.span n _ hY
    refine ⟨fun i => mulF P LL (r i), fun i => mulF_mem_fil P LL K (hr i), ?_⟩
    have e1 := coordF_sm P LL m (GlobalTheory.DRFil.idem P.R.BdR τ')
      (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j)
    rw [mulF_idem P LL K τ' hτ, one_smul, hcY] at e1
    rw [← e1, he, map_sum]
    exact Finset.sum_congr rfl fun i _ => coordF_sm P LL m (r i) (d i)
  have htop : ⊤ ≤ Submodule.span P.R.BdR (Set.range u') := by
    rintro y -
    choose f hf using fun j => (P.PD K).Fil_exh (y j)
    have hn : ∀ j, y j ∈ (P.PD K).Fil (-(∑ j, |f j|)) := by
      intro j
      have hle : -(∑ j, |f j|) ≤ f j := by
        have h1 : |f j| ≤ ∑ j, |f j| :=
          Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
        have h2 := neg_abs_le (f j)
        linarith
      exact SetLike.le_def.1 (GlobalTheory.DRFil.fil_antitone (P.PD K) hle) (hf j)
    obtain ⟨c, -, hc⟩ := hspan' _ y hn
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  letI : Field P.R.BdR := (GlobalTheory.DRFil.isField_dR T).toField
  have hle1 : m ≤ m' := by
    have h1 := finrank_range_le_card (R := P.R.BdR) u'
    rw [Set.finrank, eq_top_iff.2 htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hle2 : m' ≤ m := by
    have := GlobalTheory.Per.Components.card_le_of_idem_indep (GlobalTheory.DRFil.idem_mul_idem (F := P.R.BdR) τ')
      (GlobalTheory.DRFil.idem_ne_zero (F := P.R.BdR) τ')
      (fun i j => GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥LL.1 (Fin m)).coord j) (d i))
      (fun r hr => had.indep r (by
        rw [GlobalTheory.DRFil.eq_sum_basis (Pi.basisFun ↥LL.1 (Fin m))
          (∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) (r i) (d i))]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [map_sum]
        simp only [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self]
        rw [hr j, map_zero, LinearMap.zero_apply]))
    simpa using this
  obtain rfl : m = m' := le_antisymm hle1 hle2
  have hind : LinearIndependent P.R.BdR u' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨u', k, fun a => ?_, fun i j => coordF_mem_fil P LL m K (had.mem i).2 j, fun g hg i => ?_,
    hspan', hind⟩
  · rw [had.multV_eq a, Multiset.count_map]
    simp [Finset.sum_boole, eq_comm]
    rfl
  · have h1 := coordF_act P LL m K r' g hg (d i)
    rw [((GlobalTheory.DRFil.mem_DdR (P.PD K) (repOf r') (d i)).1 (had.mem i).1.1) g] at h1
    exact h1.symm

end GlobalTheory.HTBasis

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

theorem GlobalTheory.HTBasis.htc_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = Module.finrank ℚ_[l] ↥K.1 * m → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI T K LL m r' ρ hdR τ' hτ K' _hK hL
  obtain ⟨u, k, hcount, hmem, heq, hspan, hind⟩ :=
    GlobalTheory.HTBasis.exists_dR_frame l P AI T K LL m r' hdR τ' hτ
  have hU := GlobalTheory.T.hodgeTateSymbolMatrix_isUnit_det (GlobalTheory.HTBasis.thetaOf T) u k hmem hspan hind
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hU).unit, k, hcount, fun g hg => ?_⟩
  have hfix : ∀ x ∈ LL.1, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (hL hx)
  exact GlobalTheory.T.hodgeTateSymbolMatrix_equivariant (GlobalTheory.HTBasis.thetaOf T) r' u k hmem g (heq g hfix)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationDualityStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_filtration_duality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, drDualCore (P.PD K) ∧ Formalism.MainNotions.LocalSituation.filDualCore (P.PD K) := by
  first | exact @GlobalTheory.TateDualTied.main | exact GlobalTheory.TateDualTied.main | (intros; apply GlobalTheory.TateDualTied.main <;> assumption)
end

