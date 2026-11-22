import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0812
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsRealisesNeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardFrameKeepsMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.MtRead.IdFrameStd

variable {D : D7}

open GlobalTheory.StdFrameExist in

theorem exists_idFrame_of (hF : D.host.F = maximalRealSubfield D.host.E) (V : HSp D) (hg : V.gram = 1)
    (hV : Seed.FrmC.StdLat V) (n : ℕ) (hn : V.rank = n) :
    ∃ P : principalLevelFrame.RowPsi V n, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  subst hn
  have hO : IsOrthF V (1 : GL (Fin V.rank) (Lev.EAf D)) := by
    show Formalism.UG.cT (sgA D) (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) * gA V * 1 = 1
    have : gA V = 1 := by
      show V.gram.map _ = 1
      rw [hg]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]
  have hI : IntM (SI D) ((1 : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) := fun i j => by
    rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact (SI D).one_mem
    · exact (SI D).zero_mem
  refine ⟨rowPsi V 1 hO, ⟨rfl, fun κ a b => ?_⟩, stdFrame_rowPsi hF hV hO hI (by rw [inv_one]; exact hI)⟩
  rw [← GlobalTheory.HeckeTrans.finE_unswap]
  show (Formalism.IndefR.Lev.finE V (psiF V 1 hO κ)).1.map _ a b = _
  rw [finE_psiF, inv_one, mul_one, one_mul]
  rfl

theorem exists_idFrame : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (j : Fin D.R.m), FWT.VStd D j →
    ∃ P : principalLevelFrame.RowPsi (Vc D j) D.R.nV, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  intro D hF j hV
  have hL := (GlobalTheory.Equiv.StdSpace.lattice_clause_iff (Vc D j)).1 hV.2
  have hS : Seed.FrmC.StdLat (Vc D j) := fun x => by
    rw [hL]
    exact forall_congr' fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm
  exact exists_idFrame_of hF (Vc D j) hV.1 hS D.R.nV (GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne.rank_Vc j).1

end GlobalTheory.MtRead.IdFrameStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbeddingStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformiser_norm_gap_padic_embedding : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]), ∃ ϖ : F, 0 < ‖φ ϖ‖ ∧ ‖φ ϖ‖ < 1 ∧ ∀ c : F, ‖φ c‖ < 1 → ‖φ c‖ ≤ ‖φ ϖ‖ := by
  first | exact @GlobalTheory.UnifGap.exists_unif_norm_gap | exact GlobalTheory.UnifGap.exists_unif_norm_gap | (intros; apply GlobalTheory.UnifGap.exists_unif_norm_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameGenRep

open Formalism.L2.NT

theorem exists_zmod_eq {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ^ g = z) :
    ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = z := by
  first
  | exact @_root_.GlobalTheory.RangeOfPowerFixed.main
  | exact _root_.GlobalTheory.RangeOfPowerFixed.main
  | (apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RangeOfPowerFixed.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RangeOfPowerFixed.main ..)

theorem exists_rep : ∀ (D : D7), GrpSide D → ∀ (k : Fin 2) (v : D.nd.PlG k), normV (D.naut.plGw k v) = D.host.g k ∧ ∃ (u ϖ : 𝓞 D.host.E) (π : D.nd.Om), u ∉ (D.naut.plGw k v).asIdeal ∧ ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 ∧ orderOf (D.ntypes.tg k v π / π) = normV (D.naut.plGw k v) - 1 := by
  intro D hG k v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : CharZero D.nd.Om := charZero_of_injective_algebraMap (algebraMap D.host.E D.nd.Om).injective
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  have hAP : IsPlaceOver (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) :=
    D.nd.plOm.2 (D.naut.plGw k v)
  have hgP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgP
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg1 : 0 < D.host.g k - 1 := by have := hgp.two_le; omega
  have hgΩ : ((D.host.g k : ℕ) : D.nd.Om) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((D.host.g k : ℕ) : D.nd.Om) hg1
  have hT : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) = hG.ζ k 1 :=
    hG.tg_tame k v 1 one_pos π (by rw [pow_one]; exact hπ)
  have hq : D.ntypes.tg k v π / π ∈ D.nd.plOm.1 (D.naut.plGw k v) :=
    tameQuot_mem (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) hg1 hgΩ hπ
  have hpow : (D.ntypes.tg k v π / π) ^ (D.host.g k - 1) = 1 := tameQuot_pow (D.ntypes.tg k v) hgΩ hπ
  have hζ := (hG.ζ_gen k 1 one_pos).1
  rw [pow_one] at hζ
  have hζ1 : hG.ζ k 1 ^ (D.host.g k - 1) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one _
  have hζpow : hG.ζ k 1 ^ D.host.g k = hG.ζ k 1 := by
    calc _ = hG.ζ k 1 ^ (D.host.g k - 1) * hG.ζ k 1 := by rw [← pow_succ, Nat.sub_add_cancel hgp.one_le]
      _ = _ := by rw [hζ1, one_mul]
  have hζ0 : hG.ζ k 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hg1.ne'] at hζ1
    exact zero_ne_one hζ1
  obtain ⟨c, hc⟩ := exists_zmod_eq _ hζpow
  have hca : ((c.val : ℕ) : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = hG.ζ k 1 := by
    rw [← hc, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), ZMod.natCast_zmod_val]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = c.val := ⟨_, rfl⟩
  rw [← hn] at hca
  have hcast : algebraMap D.host.E D.nd.Om ((n : 𝓞 D.host.E) : D.host.E) = (n : D.nd.Om) := by
    simp
  have haA : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := natCast_mem _ _
  have hra : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (n : D.nd.Om) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) := by
    unfold redThrough; rw [dif_pos haA]
  have hra' : hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) = hG.ζ k 1 := by
    have : (⟨(n : D.nd.Om), haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) = (n : D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast, hca]
  have hrq : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, hq⟩) := by
    unfold redThrough; rw [dif_pos hq]
  have hval : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - (n : D.nd.Om)) < 1 := by
    have h1 := (hG.kv k v).injective (((hrq.symm.trans hT).trans hra'.symm))
    have h2 := Ideal.Quotient.eq.1 h1
    have h3 := ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).1 h2
    exact h3
  have hu : (n : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 := (hAP _).2 h
    have h2 : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := haA
    have h3 : (⟨_, haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ∈ IsLocalRing.maximalIdeal _ :=
      ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).2 (by rw [hcast] at h1; exact h1)
    rw [← IsLocalRing.residue_eq_zero_iff] at h3
    rw [h3, map_zero] at hra'
    exact hζ0 hra'.symm
  have hord : orderOf (D.ntypes.tg k v π / π) = D.host.g k - 1 := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow)
    rw [← hζ]
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨_, hq⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ^ orderOf (D.ntypes.tg k v π / π) = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← hT, hrq, ← map_pow, ← map_pow, h1, map_one, map_one]
  refine ⟨hN, (n : 𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E), π, hu, hgP, hspl.2.1, ?_, ?_, ?_⟩
  · rw [hN]; simpa using hπ
  · rw [hcast]; exact hval
  · rw [hN]; exact hord

end GlobalTheory.TameGenRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_point_lattice_isLattice : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (h : GA D (Vc D j)), Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) := by
  first | exact @GlobalTheory.LatFull.latAt_isLattice | exact GlobalTheory.LatFull.latAt_isLattice | (intros; apply GlobalTheory.LatFull.latAt_isLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotLeOpenSubgroup
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelGlob

theorem finite_not_ine_le_of_isOpen : ∀ (Ω : Type) [Field Ω] (k : Type) [Field k] [NumberField k] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : Subgroup (G k Ω)), IsOpen (N : Set (G k Ω)) →
    {w : HeightOneSpectrum (𝓞 k) | ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ¬ Ine (F := k) A ≤ N}.Finite := by
  intro Ω _ k _ _ _ _ N hN
  obtain ⟨L, hL, hLN⟩ := (krullTopology_mem_nhds_one_iff k Ω (N : Set (G k Ω))).1 (hN.mem_nhds N.one_mem)
  haveI : FiniteDimensional k L := hL
  refine (GlobalTheory.InertiaAlmostAll.finite_ramified k Ω L).subset ?_
  rintro w ⟨B, hB, h⟩
  exact ⟨B, hB, fun h' => h fun x hx => hLN (h' hx)⟩

end GlobalTheory.DelGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesCurveMulCoprimeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixesCurve_mul_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (m n p : ℕ) (A : ValuationSubring ℂ) (τ : ℂ ≃+* ℂ), p.Prime → (p : ℂ) ∈ A.nonunits → ¬ p ∣ n → Nat.Coprime m n → 3 ≤ m / p ^ m.factorization p → FixesCurve H τ m → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → FixesCurve H τ (m * n) := by
  first | exact @GlobalTheory.CompRat.Inertia.fixesCurve_mul | exact GlobalTheory.CompRat.Inertia.fixesCurve_mul | (intros; apply GlobalTheory.CompRat.Inertia.fixesCurve_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesMatchesRationalPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.MtReadRat

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem cT_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (σA : A →+* A) (σB : B →+* B)
    (hc : ∀ x, φ (σA x) = σB (φ x)) {m : Type} [Fintype m] [DecidableEq m] (J g : Matrix m m A) :
    Formalism.UG.cT σB (g.map φ) * J.map φ * g.map φ = (Formalism.UG.cT σA g * J * g).map φ := by
  have : Formalism.UG.cT σB (g.map φ) = (Formalism.UG.cT σA g).map φ := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [this, Matrix.map_mul, Matrix.map_mul]

variable {D : D7}

theorem finHom_entry (V : HSp D) (h : GA D V) (X : GL (Fin V.rank) D.host.E) (hX : matHom V h = Formalism.UG.bc (incA D) X)
    (a b : Fin V.rank) : (finHom V h).1 a b = inclR (F := D.host.F) (Af D.host.F) (X.1 a b) := by
  have : (finHom V h).1 a b = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V h).1 a b) := rfl
  rw [this, hX]
  simp [Formalism.UG.bc, inclR, incA]

theorem entry_of_ratF {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b))
    (κ : GAf D.host.E V.rank) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E)
    (e : Bridge.ratF V γ' = frameEquiv P κ) (hR : Bridge.IsRatMat V γ' γE) (a c : Fin V.rank) :
    ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a c =
      Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  have e' : finHom V γ'.1 = finHom V (P.ψ κ) := congrArg Subtype.val e
  have h1 := hId κ a c
  have h2 : finMat D.sp.cm.sig V.gram (P.ψ κ) a c = inclR (F := D.host.F) (Af D.host.F) (γE.val a c) := by
    show (finHom V (P.ψ κ)).1 a c = _
    rw [← e']
    exact finHom_entry V γ'.1 γE hR a c
  rw [h2] at h1
  rw [← (RingEquiv.eq_symm_apply _).1 h1]
  exact GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _

theorem ratMatch_fwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) :
    ∃ γ' : Formalism.L2.Theta.GQ V, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γ0, hγ0, e0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  have hγent : ∀ a b, (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b =
      Algebra.TensorProduct.includeLeftRingHom ((γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun a b => by
    rw [← e0]; exact Matrix.GeneralLinearGroup.map_apply _ _ _ _
  have hfin : ∀ a b, (finHom V (P.ψ γ.1)).1 a b = inclR (F := D.host.F) (Af D.host.F) ((γ0 : Matrix _ _ D.host.E) a b) :=
    fun a b => by
      show finMat D.sp.cm.sig V.gram (P.ψ γ.1) a b = _
      rw [hId]
      simp only [Fin.cast_eq_self]
      rw [hγent, RingEquiv.symm_apply_eq]
      exact (GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _).symm

  have hsnd : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (sigR (AF D.host.F) D.sp.cm.sig x) =
      sigR (Af D.host.F) D.sp.cm.sig ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom x) :=
    fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hUA := (P.ψ γ.1).2
  change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((P.ψ γ.1).1.1) * JR (AF D.host.F) V.gram * (P.ψ γ.1).1.1 =
    JR (AF D.host.F) V.gram at hUA
  have hUf := congrArg (fun M => M.map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) hUA
  rw [← cT_map _ _ _ hsnd] at hUf
  have hM : ((P.ψ γ.1).1.1 : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      (γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; exact hfin a b
  have hJ : (JR (AF D.host.F) V.gram).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      V.gram.map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; simp [JR, inclR]
  have hci : ∀ (R : Type) [CommRing R] [Algebra D.host.F R] (x : D.host.E),
      inclR (F := D.host.F) R (D.sp.cm.sig x) = sigR R D.sp.cm.sig (inclR (F := D.host.F) R x) := fun R _ _ x => by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  rw [hM, hJ, cT_map _ _ _ (hci (Af D.host.F))] at hUf
  have hγ0' : γ0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := Matrix.map_injective hinjR hUf
  have hHR : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ0 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * (γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [JR, cT_map _ _ _ (hci (AF D.host.F))]
    exact congrArg (fun M => Matrix.map M (inclR (F := D.host.F) (AF D.host.F))) hγ0'
  refine ⟨⟨⟨_, hHR⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ0, hγ0', rfl⟩)⟩, Subtype.ext (Units.ext ?_)⟩
  ext a b
  refine (finHom_entry V ⟨_, hHR⟩ γ0 rfl a b).trans ?_
  exact (hfin a b).symm

theorem ratMatch_bwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ' : Formalism.L2.Theta.GQ V) :
    ∃ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γE, hγE, eE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ'.2)
  have hR : Bridge.IsRatMat V γ' γE := eE.symm
  set κ := (frameEquiv P).symm (Bridge.ratF V γ') with hκ
  have he : Bridge.ratF V γ' = frameEquiv P κ := ((frameEquiv P).apply_symm_apply _).symm
  have hent := key κ γ' γE he hR
  have hmat : ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
      (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom := by
    ext a c; exact hent a c
  have hU := κ.2
  simp only [ReciprocityTheory.Aut.GA, ReciprocityTheory.Aut.UGroup, Subgroup.mem_mk, Set.mem_ofPred_eq] at hU
  have hc : ∀ x : D.host.E, (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)
      ((IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x) =
      ReciprocityTheory.Aut.conjAL D.host.E (Algebra.TensorProduct.includeLeftRingHom x) := fun x => by
    simp [ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.map_tmul]
  have hcT : ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
      ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom) =
      (ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) (γE : Matrix _ _ _)).map
        Algebra.TensorProduct.includeLeftRingHom := by
    ext i j; simp only [ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply, hc]
  have h0 : γE ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
    show (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) γE = 1
    apply Matrix.map_injective hinjL
    simp only
    rw [Matrix.map_mul, ← hcT, ← hmat, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hU
  refine ⟨⟨κ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γE, h0, Units.ext ?_⟩)⟩, he⟩
  rw [hmat]
  ext a c
  exact Matrix.GeneralLinearGroup.map_apply _ _ _ _

end GlobalTheory.MtReadRat

namespace GlobalTheory.MtRead
open GlobalTheory.MtReadRat Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem ratMatch_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → RatMatch (frameEquiv P) ∧ ∀ (hn : V.rank = n) (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.ratF V γ' = frameEquiv P γ → Bridge.IsRatMat V γ' γE → ∀ a c, (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c) = Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  intro D V n hF P ⟨hn, hId⟩
  subst hn
  refine ⟨⟨ratMatch_fwd hF P hId, ratMatch_bwd hF P hId⟩, fun hn γ γ' γE e hR a c => ?_⟩
  simpa only [Fin.cast_eq_self] using entry_of_ratF hF P hId γ.1 γ' γE e hR a c

end GlobalTheory.MtRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullDegreeLabelForcesTrivialWildInertiaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_degree_label_forces_trivial_wild_inertia : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.TypeLeaf.WildOne D := by
  first | exact @GlobalTheory.WildFull.main | exact GlobalTheory.WildFull.main | (intros; apply GlobalTheory.WildFull.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_hodge_of_cuspidal : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.GalOfCusp.LocalGlobalAboveL → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), CGTrue hL D T → GlobalTheory.TripleLocal.GalHodge D T ∧ GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisReps D := by
  first | exact @GlobalTheory.HodgeOfTrue.galHodge_galoisReps_of_cgTrue | exact GlobalTheory.HodgeOfTrue.galHodge_galoisReps_of_cgTrue | (intros; apply GlobalTheory.HodgeOfTrue.galHodge_galoisReps_of_cgTrue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormReadingEqGoodModelVectorEvaluationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  first | exact @GlobalTheory.SeriesTie.rd_good_model | exact GlobalTheory.SeriesTie.rd_good_model | (intros; apply GlobalTheory.SeriesTie.rd_good_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodIdempotentIrreducibleCharacterGenericSumNeZeStatement
section
open Formalism.BasicNotions GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_idempotent_irreducible_character_generic_sum_ne_zero : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)] (U : Subgroup (G0g D.nd)) [Fintype U], U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r → ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ → 2 ≤ D.R.r → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0 := by
  first | exact @GlobalTheory.WhittakerMeets.sum_ne_zero | exact GlobalTheory.WhittakerMeets.sum_ne_zero | (intros; apply GlobalTheory.WhittakerMeets.sum_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystemStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_part_eigensystem_is_triple_eigensystem : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), NoFormsOff D → MeetsAll D → CommAll D → FullAll D → D.nexp.sig_all := by
  first | exact @GlobalTheory.TwInputs.EigAll.sig_all_of_sideB | exact GlobalTheory.TwInputs.EigAll.sig_all_of_sideB | (intros; apply GlobalTheory.TwInputs.EigAll.sig_all_of_sideB <;> assumption)
end

