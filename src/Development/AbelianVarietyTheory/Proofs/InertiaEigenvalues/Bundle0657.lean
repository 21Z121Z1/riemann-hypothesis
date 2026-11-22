import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0394
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaJEqZeroOfUntwisted
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory

theorem etaJ_eq_zero_of_untwisted (D : D7) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : D.what₂.muAt w = D.what₂.mu0) : D.what₂.etaJ j w = 0 := by
  rw [D.etaJ_tie j w h1 h2]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact absurd (by rw [((D.nd.locs_mem j w i).1 hi).2]; exact hw) (D.nd.w_tw i)

theorem etaJ_join : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → (∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w) → (∀ i, SpecPr D i) → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hH hLat hSpec i w
  have hj1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left _ _
  have hj2 : (i : ℕ) + 1 ≤ D.R.m := Nat.lt_of_lt_of_le i.2 hm
  by_cases h : D.plEq w ∈ S0.Tw
  · rw [if_pos h]
    have hne : D.what₂.muAt w ≠ D.what₂.mu0 := by
      rw [hTup.muAt w, ← hTup.mu0]
      exact fun e => (hTw _).1 h (hTup.inj e)
    have htw : D.what₂.muTw w = tup (S0.μ (D.plEq w)) :=
      ((D.what₂.muAt_or w).resolve_left hne).symm.trans (hTup.muAt w)
    obtain ⟨hM1, hM2, hM3⟩ := hMt i _ h
    obtain ⟨hZ, hE⟩ := GlobalTheory.T.rationalFormLength_eq_definiteFamily D G Pl0 T m A P ψ Zs tup eMt s hOk i (S0.μ (D.plEq w)) hM1 hM2 hM3
    rw [GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength D M Tn ((i : ℕ) + 1) w hj1 hj2 hne hH (hLat _ w hj1 hj2 hne) (htw ▸ hZ)
      (fun i' _ => hSpec i'), htw]
    exact hE w
  · rw [if_neg h]
    refine etaJ_eq_zero_of_untwisted D _ w hj1 hj2 ?_
    rw [hTup.muAt w, ← hTup.mu0]
    congr 1
    by_contra hn
    exact h ((hTw _).2 hn)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlaceOff

open Formalism.HermitianLattices.Ext.L3

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isConjPl_iff (D : D7) (P Q : PlE D.host) :
    IsConjPl D.host P Q ↔ ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ conjO D.host.E x ∈ Q.asIdeal := by
  constructor
  · intro h x
    exact h x (conjO D.host.E x) (by rw [conjO_coe, star_eq_hostConj])
  · intro h x y hy
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    subst this
    exact h x

noncomputable def conjPl (D : D7) (P : PlE D.host) : PlE D.host where
  asIdeal := P.asIdeal.comap (conjO D.host.E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : conjO D.host.E x ∈ P.asIdeal.comap (conjO D.host.E) := by
      rw [Ideal.mem_comap, conjO_conjO]; exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← conjO_conjO (K := D.host.E) x, this, map_zero]

theorem mem_conjPl (D : D7) (P : PlE D.host) (x : 𝓞 D.host.E) :
    x ∈ (conjPl D P).asIdeal ↔ conjO D.host.E x ∈ P.asIdeal := Iff.rfl

theorem conjPl_conjPl (D : D7) (P : PlE D.host) : conjPl D (conjPl D P) = P := by
  ext x
  rw [mem_conjPl, mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl (D : D7) (P : PlE D.host) : IsConjPl D.host P (conjPl D P) := by
  rw [isConjPl_iff]
  intro x
  rw [mem_conjPl, conjO_conjO]

theorem isConjPl_conjPl' (D : D7) (P : PlE D.host) : IsConjPl D.host (conjPl D P) P := by
  rw [isConjPl_iff]
  intro x
  rfl

theorem conjIdeal_eq (D : D7) (P : PlE D.host) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (conjPl D P).asIdeal :=
  conjIdeal_eq_comap _

theorem isSplitPl_iff (D : D7) (P : PlE D.host) :
    IsSplitPl D.host P ↔ ∃ x : 𝓞 D.host.E, x ∈ P.asIdeal ∧ conjO D.host.E x ∉ P.asIdeal := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, h _ (by rw [conjO_coe, star_eq_hostConj])⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun y hy => ?_⟩
    have : y = conjO D.host.E x := RingOfIntegers.ext (by rw [hy, conjO_coe, star_eq_hostConj])
    rw [this]; exact h

theorem conjPl_ne_of_split (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    (conjPl D P).asIdeal ≠ P.asIdeal := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  intro he
  apply hcx
  rw [← mem_conjPl, he]
  exact hx

theorem isSplitPl_conjPl (D : D7) {P : PlE D.host} (h : IsSplitPl D.host P) :
    IsSplitPl D.host (conjPl D P) := by
  obtain ⟨x, hx, hcx⟩ := (isSplitPl_iff D P).1 h
  rw [isSplitPl_iff]
  refine ⟨conjO D.host.E x, ?_, ?_⟩
  · rw [mem_conjPl, conjO_conjO]; exact hx
  · rw [mem_conjPl, conjO_conjO]; exact hcx

theorem exists_conj_off (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E))
    (P : PlE D.host)
    (hS0 : ∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0)
    (h2 : placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)))
    (hb : ∀ Q ∈ Sb, Q ∈ S0) (hP : IsSplitPl D.host P) (hPS : P ∉ S0) :
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  have hP'S : conjPl D P ∉ S0 := fun h => hPS (hS0 _ _ h (isConjPl_conjPl' D P))
  have hne := conjPl_ne_of_split D hP
  refine ⟨conjPl D P, isConjPl_conjPl D P, isSplitPl_conjPl D hP, hP'S, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [conjIdeal_eq]; exact hne, fun h => hPS (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq] at he
    have : Q = conjPl D P := HeightOneSpectrum.ext he
    exact hP'S (this ▸ hb Q (by exact_mod_cast hQ))
  · refine ⟨by rw [conjIdeal_eq, conjPl_conjPl]; exact hne.symm,
      fun h => hP'S (hb _ (by exact_mod_cast h)), ?_⟩
    intro Q hQ he
    rw [conjIdeal_eq, conjPl_conjPl] at he
    have : Q = P := HeightOneSpectrum.ext he
    exact hPS (this ▸ hb Q (by exact_mod_cast hQ))
  · exact fun h => hPS (h2 h)
  · exact fun h => hP'S (h2 h)

end GlobalTheory.ConjPlaceOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDisc
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.SeedExists

theorem exists_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ),
    (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T),
    Nonempty (Seed bk d (fun g => LinearMap.toMatrix b b (actT L g)) τ) := by
  intro l _ K bk τ hτ P AI hstd V _ _ _ _ _ _ _ ρ L _ hcrys d b
  obtain ⟨T⟩ := hstd
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  set ρm : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l] := fun g => LinearMap.toMatrix b b (actT L g) with hρm
  have hv0 := GlobalTheory.T.crystallineLattice_basis_span_invariants l K P AI T V ρ L hcrys d b
  obtain ⟨U, U', hUU', hU⟩ := GlobalTheory.T.exists_invertible_invariant_periodMatrix_bcris l K P AI T d ρm hv0
  obtain ⟨hInvB, hInvdR⟩ := GlobalTheory.T.periodRingCore_crystalline_deRham_invariants l P AI T C hC
  obtain ⟨c₁, c₃, F, F', hFF', hF⟩ := GlobalTheory.T.exists_frobeniusMatrix_crystallineModule_over_witt l K bk C hInvB d ρm U U' hUU' hU
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.T.bcris_periodMatrix_over_acris l K P AI T C hC bk d ρm U U' hUU' hU c₁ F hF
  have hv2 := GlobalTheory.T.crysLattice_basis_mem_sum_deRham_filtration l K P AI T V ρ L hcrys d b
  obtain ⟨N, m, k, c, β, hN, hk, hUN, hUc, hβ, hUcβ⟩ :=
    GlobalTheory.T.exists_bdRPlus_lattice_generators_ddR l K P AI T C hC hInvdR d ρm U U' hUU' hU hv2 N₀
  have hUU'ι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨c₂, X, X', hXX', hnp, hX, hX'⟩ :=
    GlobalTheory.T.exists_modification_of_filtration_alt l K bk C d (U.map C.ι) (U'.map C.ι) hUU'ι N m k c β hk (fun r s => hUN r s) hUc hβ hUcβ
  obtain ⟨Z, Z', hZ⟩ := hN₀ N hN X X' hX hX'
  exact GlobalTheory.T.crystallineLatticeDiscPeriodData_of_acris_periods l K bk C τ hτ d ρm N c₁ c₂ c₃ F F' X X' hFF' hXX' hnp Z Z' hZ

end GlobalTheory.SeedExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRep
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def homSpace : Submodule ℂ (Y →ₗ[ℂ] X) where
  carrier := {φ | ∀ h v, φ (ρ h v) = τ (1, h) (φ v)}
  add_mem' := by
    intro a b ha hb h v
    simp [ha h v, hb h v]
  zero_mem' := by intro h v; simp
  smul_mem' := by
    intro c a ha h v
    simp [ha h v]

theorem commute_apply (g : G) (h : H) (x : X) : τ (g, 1) (τ (1, h) x) = τ (1, h) (τ (g, 1) x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

theorem apply_pair (g : G) (h : H) (x : X) : τ (g, h) x = τ (g, 1) (τ (1, h) x) := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

def homRep : Representation ℂ G (homSpace τ ρ) where
  toFun g :=
    { toFun := fun φ => ⟨(τ (g, 1)).comp φ.1, fun h v => by
        simp only [LinearMap.comp_apply]
        rw [φ.2 h v, commute_apply]⟩
      map_add' := fun φ ψ => by ext; simp
      map_smul' := fun c φ => by ext; simp }
  map_one' := by
    ext φ v
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    simp [this]
  map_mul' a b := by
    ext φ v
    have : ((a * b, (1 : H)) : G × H) = (a, 1) * (b, 1) := by simp
    show τ (a * b, 1) _ = τ (a, 1) (τ (b, 1) _)
    rw [this, map_mul, Module.End.mul_apply]

@[simp] theorem homRep_apply_coe (g : G) (φ : homSpace τ ρ) :
    ((homRep τ ρ g φ : homSpace τ ρ) : Y →ₗ[ℂ] X) = (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) := rfl

def evMap : (extTensor (homRep τ ρ) ρ).IntertwiningMap τ where
  toLinearMap := TensorProduct.lift (homSpace τ ρ).subtype
  isIntertwining' gh := by
    apply TensorProduct.ext'
    intro φ v
    obtain ⟨g, h⟩ := gh
    simp only [LinearMap.comp_apply, extTensor_tmul, TensorProduct.lift.tmul, Submodule.subtype_apply,
      homRep_apply_coe]
    rw [φ.2 h v, ← apply_pair]

@[simp] theorem evMap_tmul (φ : homSpace τ ρ) (v : Y) :
    evMap τ ρ (φ ⊗ₜ v) = (φ : Y →ₗ[ℂ] X) v := rfl

end GlobalTheory.TensorFactor

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def diffMap (g : G) (φ : homSpace τ ρ) :
    ρ.IntertwiningMap (τ.comp (MonoidHom.inr G H)) where
  toLinearMap := (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) - (φ : Y →ₗ[ℂ] X)
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.inr_apply, map_sub]
    rw [φ.2 h v, commute_apply]

theorem homRep_eq_of_apply_eq [ρ.IsIrreducible] {g : G} {φ : homSpace τ ρ} {y : Y} (hy : y ≠ 0)
    (h : τ (g, 1) ((φ : Y →ₗ[ℂ] X) y) = (φ : Y →ₗ[ℂ] X) y) : homRep τ ρ g φ = φ := by
  rcases Representation.IsIrreducible.injective_or_eq_zero (diffMap τ ρ g φ) with hi | h0
  · refine absurd (hi (a₁ := y) (a₂ := 0) ?_) hy
    simp [diffMap, h]
  · apply Subtype.ext
    ext v
    have := congrArg (fun f => f v) h0
    simpa [diffMap, sub_eq_zero] using this

end GlobalTheory.TensorFactor

open GlobalTheory.TensorFactor in

theorem GlobalTheory.TensorFactor.exists_equiv_extTensor : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  intro G H X Y _ _ _ _ _ _ _ _ _ _ τ ρ hτs hτ hρ hinj hex
  obtain ⟨ι, hι0, hι⟩ := hex
  haveI := hτ
  haveI := hρ
  have hev : Function.Injective (evMap τ ρ) := hinj (homSpace τ ρ) fun φ hφ => hφ
  let ι' : homSpace τ ρ := ⟨ι, hι⟩
  obtain ⟨y0, hy0⟩ : ∃ v, ι v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hι0 (LinearMap.ext h)
  have hy0' : y0 ≠ 0 := fun h => hy0 (by simp [h])
  have hsurj : Function.Surjective (evMap τ ρ) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (evMap τ ρ)).resolve_right fun h0 =>
      hy0 (by simpa [ι'] using congrArg (fun f => f (ι' ⊗ₜ y0)) h0)
  refine ⟨homSpace τ ρ, inferInstance, inferInstance, homRep τ ρ, ?_, ?_,
    ⟨(Representation.IntertwiningMap.ofBijective (evMap τ ρ) ⟨hev, hsurj⟩).symm⟩⟩
  · refine isSmooth_of_nhds fun φ => ?_
    have hc : Continuous fun g : G => ((g, (1 : H)) : G × H) := by fun_prop
    refine Filter.mem_of_superset (((hτs ((φ : Y →ₗ[ℂ] X) y0)).preimage hc).mem_nhds ?_)
      fun g hg => homRep_eq_of_apply_eq τ ρ hy0' hg
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    show τ ((1 : G), (1 : H)) _ = _
    simp [this]
  · haveI : Nontrivial (Subrepresentation (homRep τ ρ)) := ⟨⊥, ⊤, fun h => by
      have h1 : ι' ∈ (⊤ : Subrepresentation (homRep τ ρ)).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      have h2 : ι' = 0 := (Submodule.mem_bot ℂ).1 h1
      exact hι0 (congrArg Subtype.val h2)⟩
    refine ⟨fun S => ?_⟩
    let U : Subrepresentation τ :=
      { toSubmodule :=
          LinearMap.range ((evMap τ ρ).toLinearMap ∘ₗ LinearMap.rTensor Y S.toSubmodule.subtype)
        apply_mem_toSubmodule := by
          rintro ⟨g, h⟩ _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul ψ z =>
            refine ⟨⟨homRep τ ρ g ψ, S.apply_mem_toSubmodule g ψ.2⟩ ⊗ₜ ρ h z, ?_⟩
            show ((homRep τ ρ g ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) (ρ h z) =
              τ (g, h) (((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z)
            rw [homRep_apply_coe, LinearMap.comp_apply, (ψ : homSpace τ ρ).2 h z, ← apply_pair]
          | add a b ha hb =>
            rw [map_add, map_add]
            exact add_mem ha hb }
    rcases IsSimpleOrder.eq_bot_or_eq_top U with hU | hU
    · left
      apply Subrepresentation.toSubmodule_injective
      refine eq_bot_iff.2 fun ψ hψ => (Submodule.mem_bot ℂ).2 (Subtype.ext (LinearMap.ext fun z => ?_))
      have hm : (evMap τ ρ).toLinearMap (LinearMap.rTensor Y S.toSubmodule.subtype (⟨ψ, hψ⟩ ⊗ₜ z)) ∈
          U.toSubmodule := ⟨⟨ψ, hψ⟩ ⊗ₜ z, rfl⟩
      rw [hU] at hm
      have h2 := (Submodule.mem_bot ℂ).1 hm
      have h3 : ((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z = 0 := by simpa using h2
      simpa using h3
    · right
      apply Subrepresentation.toSubmodule_injective
      refine eq_top_iff.2 fun φ _ => ?_
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy0'
      let P : homSpace τ ρ ⊗[ℂ] Y →ₗ[ℂ] homSpace τ ρ :=
        (TensorProduct.rid ℂ (homSpace τ ρ)).toLinearMap ∘ₗ LinearMap.lTensor (homSpace τ ρ) l
      have hP : ∀ t, P (LinearMap.rTensor Y S.toSubmodule.subtype t) ∈ S.toSubmodule := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul ψ z => simpa [P] using S.toSubmodule.smul_mem (l z) ψ.2
        | add a b ha hb =>
          rw [map_add, map_add]
          exact add_mem ha hb
      have hmem : evMap τ ρ (φ ⊗ₜ y0) ∈ U.toSubmodule := by
        rw [hU]
        exact Submodule.mem_top
      obtain ⟨t, ht⟩ := hmem
      have ht' : LinearMap.rTensor Y S.toSubmodule.subtype t = φ ⊗ₜ y0 :=
        hev (a₁ := LinearMap.rTensor Y S.toSubmodule.subtype t) (a₂ := φ ⊗ₜ y0) ht
      have := hP t
      rw [ht'] at this
      simpa [P, hl] using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRham
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BstLog

theorem iota_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧
      (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  intro l _ P AI T
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_log_tilt_kummerCoboundary_BdR l P AI T
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  let ι : Bst P →ₐ[ℚ_[l]] P.R.BdR := Polynomial.eval₂AlgHom P.ιB u (fun _ => Commute.all _ _)
  refine ⟨ι, fun b => Polynomial.eval₂_C _ _, fun g x => ?_⟩
  have h : ι.comp (actSt P g) = ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →ₐ[ℚ_[l]] P.R.BdR).comp ι := by
    apply Polynomial.algHom_ext'
    · ext b
      show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g (Polynomial.C b)) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (Polynomial.C b))
      rw [actSt_C, Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact hcomm g b
    · show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g Polynomial.X) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u Polynomial.X)
      rw [actSt_X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, hu]
      rfl
  exact congrArg (fun F : Bst P →ₐ[ℚ_[l]] P.R.BdR => F x) h

end GlobalTheory.BstLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleQuotientFinitelyGeneratedRep
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.IrrQuot

theorem main : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (s : Finset V), Nontrivial V → Submodule.span ℂ {w | ∃ g : G, ∃ v ∈ s, w = ρ g v} = ⊤ → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), τ.IsIrreducible ∧ ∃ f : ρ.IntertwiningMap τ, Function.Surjective f := by
  intro G V _ _ _ ρ s hV hspan
  have key : ∀ T : Subrepresentation ρ, (∀ v ∈ s, v ∈ T.toSubmodule) → T = ⊤ := by
    intro T hT
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro w ⟨g, v, hv, rfl⟩
    exact T.apply_mem_toSubmodule g (hT v hv)
  haveI : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule := by
    let t : Finset ρ.asModule := s
    refine ⟨⟨t, ?_⟩⟩
    have h := key (Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)))
      (fun v hv => Submodule.subset_span (R := MonoidAlgebra ℂ G) (s := (t : Set ρ.asModule)) hv)
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)) := by
      rw [h]; trivial
    exact hx
  haveI : IsCoatomic (Subrepresentation ρ) :=
    (OrderIso.isCoatomic_iff Subrepresentation.subrepresentationSubmoduleOrderIso).2 inferInstance
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← h] at this
    exact hv this
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  refine ⟨_, inferInstance, inferInstance, GlobalTheory.SmGL.subQuot ⊤ M, GlobalTheory.SmGL.isIrreducible_subQuot hM.covBy_top, ?_⟩
  refine ⟨⟨(Submodule.mkQ _).comp (LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id (fun _ => trivial)), fun g => rfl⟩, ?_⟩
  intro y
  obtain ⟨⟨v, _⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨v, rfl⟩

end GlobalTheory.IrrQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistablePeriodMatrixOfIsSemistableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semistable_period_matrix_of_isSemistable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∃ Q : GL n (Bst P), ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q := by
  first | exact @GlobalTheory.PMon.exists_periodMatrix_of_isSst | exact GlobalTheory.PMon.exists_periodMatrix_of_isSst | (intros; apply GlobalTheory.PMon.exists_periodMatrix_of_isSst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseAStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_rules_criterion_odd_root_of_unity_caseA : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.ExpansionsOdd.main | exact GlobalTheory.ExpansionsOdd.main | (intros; apply GlobalTheory.ExpansionsOdd.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionSubMemFiltrationZeroOfMonodromyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisAction_sub_mem_filtrationZero_of_monodromy : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b - b ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.gb_sub_b_mem_filZero | exact GlobalTheory.BKGal.gb_sub_b_mem_filZero | (intros; apply GlobalTheory.BKGal.gb_sub_b_mem_filZero <;> assumption)
end

