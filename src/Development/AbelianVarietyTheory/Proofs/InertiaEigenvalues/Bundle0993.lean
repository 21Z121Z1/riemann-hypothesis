import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0984
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0981
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0799
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0986

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelTwistCharacterMemCoefficientIntegers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceRead.LevVal

variable {D : D7}

theorem mem_intLL_of_pow {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) (hz : ∃ y, D.what₂.embLL y = z) : z ∈ intLL D := by
  obtain ⟨y, rfl⟩ := hz
  have h1 : y ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral ℤ y := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  exact ⟨⟨y, hi⟩, rfl⟩

theorem mem_range_of_pow_of_fixed {K : Type} [Field K] [Countable K] [CharZero K] (f : K →+* ℂ) {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (h : z ^ n = 1) (hf : ∀ τ : ℂ ≃+* ℂ, (∀ x, τ (f x) = f x) → τ z = z) : ∃ y, f y = z := by
  letI : Algebra K ℂ := f.toAlgebra
  have hi : IsIntegral K z := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  let L := IntermediateField.adjoin K {z}
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hi
  haveI : Countable L := (Module.finBasis K L).equivFun.toEquiv.injective.countable
  let r : L := ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
  obtain ⟨y, hy⟩ := GlobalTheory.CompRat.FixedConst.mem_range_of_fixed (K := K) L.val (r := r) (IsIntegral.of_finite K r) hf
  exact ⟨y, congrArg Subtype.val hy⟩

theorem twistOf_good {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hψ : TwOK i k Q ψ) (f : D.ntw.Ok i k →+* ℂ) :
    (twistOf ρ.rc f (ρ.ch i) Q ψ).Good ∧
      ∀ x, ∃ σ, (((twistOf ρ.rc f (ρ.ch i) Q ψ).chi x : Circle) : ℂ) = f (ψ σ : (D.ntw.Ok i k)ˣ) ∧ ∃ n ≠ 0, ψ σ ^ n = 1 := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D D.nd D.ntw ρ hρ i j b Q hsplit hdisj
  let g : (D.ntw.Ok i k)ˣ →* Circle := unitPart.comp (Units.map f.toMonoidHom)
  have hkey : charOf ρ.rc f ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (D.ntw.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, ?_⟩
  · show (⟨half (ρ.ch i) Q, charOf ρ.rc f ψ, resOf (charOf ρ.rc f ψ)⟩ : Twist D Circle).Good
    rw [hkey]
    refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D D.nd D.ntw ρ.rc hρ.rc Circle (g.comp ψ) (D.ntw.l i) (D.ntw.lPrime i).out
      (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
    · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        rw [MonoidHom.comp_apply, hx, map_one]) hopen
    · intro x x' hx
      show g (ψ x') = (g (ψ x))⁻¹
      rw [hanti x x' hx, map_inv]
    · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
      exact h3.mono (Finset.subset_union_right.trans h2)
    · intro P hP hl
      exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (D.ntw.l i) from hl))
    · intro v hv hnc B hB σ hσ
      have hvQ : v ∉ Q := by
        intro hvQ
        by_cases hc : v ∈ ρ.ch i
        · exact hv (mem_half.2 ⟨hvQ, hc⟩)
        · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
          have hv'Q : v' ∈ Q := GlobalTheory.TwistGood.ramExactly_conj D.ntw ψ _ hanti hram v hvQ v' hv'
          have hne := ne_of_split (hsplit v hvQ) hv'
          have hv'c : v' ∈ ρ.ch i := by
            by_contra h
            exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
          exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
      have h1 : ψ σ = 1 := by
        by_contra h
        exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
      rw [MonoidHom.comp_apply, h1, map_one]
  · intro x
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
    exact ⟨σ, charOf_eq ρ.rc f hopen hσ (pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero) (hpow σ), _,
      pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero, hpow σ⟩

theorem de_chi_eq_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) ∧
      ∃ n ≠ 0, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ n = 1 := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_, _, Subgroup.FiniteIndex.index_ne_zero, hpow σ⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

variable {X : RealSide D} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀)

theorem de_mem_intLL (hX : FieldOk X) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    (((Z.ρ.B i j b).de.chi x : Circle) : ℂ) ∈ intLL D := by
  obtain ⟨σ, hσ, n, hn, hp⟩ := de_chi_eq_pow Z.good i j b x
  have hz : (((Z.ρ.B i j b).de.chi x : Circle) : ℂ) ^ n = 1 := by
    rw [hσ, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hp, Units.val_one, map_one, map_one]
  haveI : Countable D.what₂.LL := (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.injective.countable
  obtain ⟨y, hy⟩ := mem_range_of_pow_of_fixed (embLL0 D) hn hz fun τ hτ => by
    rw [hσ]
    refine GlobalTheory.DeltaFixed.aut_fixes_delta_values Z.ρ Z.good i j b (X.R.C.delAt (D.ntw.l i)) (Z.pin.delta i j b) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [hX.vals.del', hX.vals.del]
  exact mem_intLL_of_pow hn hz ⟨y, hy⟩

theorem muC_mem_intLL (hX : FieldOk X) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E}
    (hPP : PP ∈ (Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) : (((Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ intLL D := by
  obtain ⟨k, hk⟩ := Z.good.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hX.roots k _ hz
  have h2 := (D.host.g_prime k).two_le
  exact mem_intLL_of_pow (Nat.mul_ne_zero (by omega) (by omega)) hz ⟨x, hx⟩

theorem levLam_twVia_mem_intLL : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ k : (baseOf Z c w j).levJ (twVia Z.ρ ι), (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) ∈ intLL D := by
  intro D X X0 Y S YS Z c w j H ι hι x
  obtain ⟨hg, hv⟩ := twistOf_good Z.good (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) H.ok (viaOk ι)
  have htw : ∀ z, (((twVia Z.ρ ι).chi z : Circle) : ℂ) ∈ intLL D := fun z => by
    obtain ⟨σ, hσ, n, hn, hp⟩ := hv z
    obtain ⟨y, hy⟩ := H.val σ
    refine mem_intLL_of_pow hn ?_ ⟨y, ?_⟩
    · refine (congrArg (· ^ n) hσ).trans ?_
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hp, Units.val_one, map_one]
    · rw [← hι, hy]
      exact hσ.symm
  have hext : ∀ g : G0 (Z.ρ.B (c.twI w) j (c.sd w)).G.Pg (Wc D j).rank,
      ((ext1 (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H (⇑(Z.ρ.B (c.twI w) j (c.sd w)).G.P.chi) g : ℂˣ) : ℂ) ∈ intLL D := fun g => by
    unfold ext1
    split_ifs with h
    · obtain ⟨g', rfl⟩ := (Z.ρ.eG (c.twI w) j (c.sd w)).surjective g
      obtain ⟨g₀, rfl⟩ := (X.R.eG.trans X.cG).surjective g'
      have hu : X.cG (X.R.eG g₀) ∈ D.nexp.U := ((Z.tie (c.twI w) j (c.sd w)).U_eq _).1 h
      have e1 := ((Z.tie (c.twI w) j (c.sd w)).psiU_eq ⟨_, hu⟩ h).trans (H.psi_eq (c.twI w) (c.sd w) ⟨g₀, (H.U_eq g₀).1 hu⟩ hu)
      refine mem_intLL_of_pow (n := Nat.card (Z.ρ.B (c.twI w) j (c.sd w)).G.P.H) Nat.card_pos.ne' ?_ ⟨_, (map_inv₀ _ _).trans e1.symm⟩
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
    · exact one_mem _
  have e : (baseOf Z c w j).levLam (twVia Z.ρ ι) x =
      levFn (baseOf Z c w j).F.βS ((baseOf Z c w j).levS (twVia Z.ρ ι)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hext _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem_intLL Z H.field _ j _ hPP _))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (locC_mem (Z.good.base _ j _).de (de_mem_intLL Z H.field _ j _) PP _) (locC_mem (t := twVia Z.ρ ι) hg htw PP _)

end GlobalTheory.PlaceRead.LevVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsUnitarisable
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

namespace GlobalTheory.RowSplitUnit

set_option maxHeartbeats 2000000 in

theorem finTyp_rows_locS_unitarisable : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D _ rep _ _ _ => ∀ (j : ℕ) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)), IsLocS (rep σ).S s τ ∧ GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  intro hN hL
  unfold GlobalTheory.LiftRef.AtRows
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo _ _ _ _ Rw _ M tup Q _ _ j σ _ s
  obtain ⟨hH, hF, -⟩ := hHost (w.st Z) hO
  obtain ⟨τ, hτ⟩ := GlobalTheory.RowLocalRows2.finTyp_rows_exists_isLocS hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hHo hH hF σ s
  obtain ⟨Bf, k1, k2, k3, k4⟩ := GlobalTheory.RowSphSmall.exists_form_rowRepR hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  exact ⟨τ, hτ, GlobalTheory.RowSphSmall.isUnitarisable_of_isLocS _ Bf k1 k2 k3 k4 s τ hτ⟩

end GlobalTheory.RowSplitUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.ConjHalfDual

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat

variable {D : D7}

theorem cA_cA_self (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig x) = a ⊗ₜ[D.host.F] x
    congr 1
    exact star_star x
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem infPart_cA_of_zero {z : AE D} (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  have key : ∀ w : AE D, infPart D (cA D w) =
      Algebra.TensorProduct.map (AlgHom.id D.host.F (Ainf D.host.F)) D.sp.cm.sig (infPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  rw [key, h, map_zero]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO; rw [hO_add_right, mul_add, map_add]

theorem hO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    hO S T x (g • y') = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, ← hx d a, map_mul]
  calc incA D (S.gram⁻¹ a b) * (cA D g * cA D (y' c b)) * incA D (T.gram c d) * (f * x d a)
      = (cA D g * f) * (incA D (S.gram⁻¹ a b) * cA D (y' c b) * incA D (T.gram c d) * x d a) := by ring
    _ = 0 := by rw [hfg, zero_mul]

theorem symplO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    symplO S T x (g • y') = 0 := by
  unfold symplO; rw [hO_eq_zero_of hfg hx, mul_zero, map_zero]

theorem mem_latO_iff_of_conjHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → e * cA D e = 0 → infPart D e = 0 → finPart D e ∈ intAE D → ∀ u : WO S T, IsHalf (cA D e) u → (u ∈ latO S T ΛS ΛT (fun _ => True) ↔ ∀ l ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e l → ψ (symplO S T l u) = 1) := by
  intro D ψ S T ΛS ΛT hψ hS hT e he hec hinf hfin u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hcc : cA D (cA D e) = e := cA_cA_self e
  have hcidem : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hcinf : infPart D (cA D e) = 0 := infPart_cA_of_zero hinf
  constructor
  · intro hmem l hl _
    have hl0 : l.map (infPart D) = 0 := by
      ext i j; exact latAll_infPart hl i j
    exact (key l hl0).1 hl u hmem
  · intro h
    have hu0 : u.map (infPart D) = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, hcinf, zero_mul]
    refine (key u hu0).2 fun u' hu' => ?_
    have hdec : u' = e • u' + (cA D e • u' + (1 - e - cA D e) • u') := by
      ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    have m1 : e • u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
      smul_mem_latAll hfin hu'
    have hh1 : IsHalf e (e • u') := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]
    have t1 : ψ (symplO S T u (e • u')) = 1 := by
      rw [GlobalTheory.SplitScalar.symplO_skew, AddChar.map_neg_eq_inv, h _ m1 hh1, inv_one]
    have t2 : symplO S T u (cA D e • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by rw [hcc]; exact hec) hu
    have t3 : symplO S T u ((1 - e - cA D e) • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by
        rw [map_sub, map_sub, map_one, hcc]
        linear_combination (-1 : AE D) * hcidem - hec) hu
    rw [hdec, symplO_add_right', symplO_add_right', t2, t3, add_zero, add_zero, t1]

end GlobalTheory.ConjHalfDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsOfReadingBoundedCuspidalHolomorphicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cuspForms_of_reading_bounded_cuspidal_holomorphic : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ w : WeightFamilies.Wt D j, w.LastPos → 8 * D.R.f * D.R.r + 4 ≤ w.n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n, rdU (T.U j T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) → f ∈ T.cuspA j (wtA w) w.n := by
  first | exact @GlobalTheory.CuspOfReading.mem_cuspA_of_rdU_mem_holSub0 | exact GlobalTheory.CuspOfReading.mem_cuspA_of_rdU_mem_holSub0 | (intros; apply GlobalTheory.CuspOfReading.mem_cuspA_of_rdU_mem_holSub0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MembersGood
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AVGood

theorem members_good (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (av : AVTied D M)
    (lv : LevelTied D M tup) (hT : TameAtG D tup) (i : D.nd.Loc) (P : D.naut.AV i) (s : SplitPlace D.host.E)
    (σ : IrrRep (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E))) (hσ : IsLocS (av.S i P) s σ) :
    Good (GlobalTheory.LocLanglands.cls σ) := by
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i P)
  have hiso : (M.loc i).real y ∈ NG.isoTyp (M.loc i).wt.ρ (av.S i P) := by
    have := hy
    rw [av.typeV i P] at this
    exact this
  have hty : (M.loc i).real y ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := by
    rw [← (M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hf0 : (M.loc i).real y ≠ 0 := fun h => hy0 ((M.loc i).real_inj (h.trans (map_zero _).symm))
  have hjr := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  by_cases hg : s.v ∈ gPl D
  · obtain ⟨k, v, s₀, hw, hv⟩ := GlobalTheory.PlaceUnderFixed.exists_splitPlace_under_plGw D s hg
    obtain ⟨ψ₀, ξ, hψ, hc, hU⟩ := lv.uni i j hj k v s₀ hw
    have hfix := GlobalTheory.UniDepthZero.main D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J (M.loc i).χ
      (M.loc i).J_open s₀ D.R.r ψ₀ ξ hU hψ (hT i j k v s₀ ξ hw hc) _ hiso hty hf0 s hv.symm σ hσ
    exact good_of_fixed_KOne hZ (GlobalTheory.SplitTypeCompl.exists_padic_equiv D s hg) _ hfix
  by_cases hp : s.v ∈ paraPl D tup i j
  · obtain ⟨s₀, ξ, hv, -, hP⟩ := lv.para i j hj s.v hp
    exact good_of_toral (GlobalTheory.ParaToral.toral_of_levelPara hBZ hZ D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J
      (M.loc i).χ (M.loc i).J_open s₀ D.R.r ξ hP _ hiso hty hf0 s hv.symm σ hσ)
  · have hB : s.v ∉ gPl D ∪ paraPl D tup i j := fun h => h.elim hg hp
    exact good_of_isSpherical hBZ _ (GlobalTheory.SphHyp.isSpherical_of_hypOutside D.host.E D.R.nV (M.loc i).wt (av.S i P) (av.irr i P) (M.loc i).J
      (M.loc i).χ (M.loc i).J_open _ (lv.hyp i j hj) _ hiso hty hf0 s hB σ hσ)

end GlobalTheory.AVGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem span_preimage_eq_top {L V W ι : Type*} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module ℂ W]
    (e : L →+* ℂ) (f : V →ₛₗ[e] W) (b : Module.Basis ι L V)
    (hli : LinearIndependent ℂ (fun i => f (b i))) (hsp : Submodule.span ℂ (Set.range (fun i => f (b i))) = ⊤)
    (S : Set W) (hS : Submodule.span ℂ S = ⊤) (hsub : ∀ y ∈ S, y ∈ Set.range f) :
    Submodule.span L {x | f x ∈ S} = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let B : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let Φ : W →ₗ[ℂ] ℂ := B.constr ℂ (fun i => e (φ (b i)))
  have key : ∀ x, Φ (f x) = e (φ x) := by
    intro x
    have hx : x ∈ Submodule.span L (Set.range b) := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have : f (b i) = B i := (Module.Basis.mk_apply hli hsp.ge i).symm
      rw [this]
      exact B.constr_basis ℂ _ i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  have hΦ : Φ = 0 := by
    refine LinearMap.ext_on hS fun y hy => ?_
    obtain ⟨x, rfl⟩ := hsub y hy
    have : φ x = 0 := hφ (Submodule.subset_span hy)
    rw [key, this, map_zero, LinearMap.zero_apply]
  apply hφ0
  ext x
  have := key x
  rw [hΦ, LinearMap.zero_apply] at this
  exact e.injective (by rw [← this, LinearMap.zero_apply, map_zero])

theorem span_latS : ∀ (D : D7) (w : D.what₂.places.Pl) (j : ℕ), Submodule.span D.what₂.LL (latS (D := D) w j) = ⊤ := by
  intro D w j
  have h := D.what₂.jMt_basis (D.what₂.muTw w) j (Module.Free.chooseBasis _ _)
  exact span_preimage_eq_top D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) _ h.1 h.2 _
    (D.what₂.MtLat (D.what₂.muTw w) j).span_top (fun y hy => D.what₂.MtLat_sub _ _ y hy)

end GlobalTheory.PlaceRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowClosureAtPrime
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem linkN_at : Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : GlobalTheory.Mem.Top.Bl.Prm hL) (C : ℝ) (CT : ℕ), 0 ≤ C → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D _ _ _ => Extra D C CT) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hP hL p C CT hC h1 h2 h3
  obtain ⟨R1, r1, e1⟩ := h1
  obtain ⟨R2, r2, e2⟩ := h2
  obtain ⟨R3, r3, e3⟩ := h3
  refine ⟨_, r1.and (r2.and r3), ?_⟩
  refine GlobalTheory.T.row_closure_linking hP _ _ C CT hC ?_ ?_
  · exact (GlobalTheory.Fc.RowE.and
      (GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) e1)
      (GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.2.1⟩) e2))
  · exact GlobalTheory.Fc.Row.strengthen (fun _ _ _ _ _ t => ⟨t.1, t.2.2.2⟩) e3

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRowsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPlace_innerProduct_classSum_rows : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → SumTw (w.st Z).toD7 M := by
  first | exact @GlobalTheory.FormInner.sumTw_rows | exact GlobalTheory.FormInner.sumTw_rows | (intros; apply GlobalTheory.FormInner.sumTw_rows <;> assumption)
end

