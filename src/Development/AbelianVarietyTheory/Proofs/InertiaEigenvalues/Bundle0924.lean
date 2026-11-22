import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0914
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0898
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0917
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLabelDeterminant

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimes
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.LocalPositionData

theorem position_data_exist : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x), AdmissibleParameterJ.JumpConditions (Fm.L x a) → ∀ l : ℕ, l.Prime → LevelStarExponents.lStar (Fm.L x a) < (l : ℝ) → (5 ≤ l ∧ (Fm.D x a).R.t + 1 < l ∧ l ≠ (Fm.D x a).host.q ∧ l ≠ (Fm.D x a).host.d ∧ l ∉ (Fm.D x a).host.small) ∧ (l ∉ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x a) → ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x a).R.m → ∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → (Fm.D x a).what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps l n (Fm.D x a).R.t h w η typ U ∧ ∀ (c : ZMod n) (b : ℤ), ((U c).count (b + w c) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c)) ∧ (U c).count (b + w c) ≤ 1) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.conductorPrimes_lt_specialPrimeThreshold_eventually Fm
  refine ⟨x0, fun x hx hx1 a _ l hl hlS => ?_⟩
  obtain ⟨hqS, hdS, hsS⟩ := hx0 x hx hx1 a
  obtain ⟨htη, hη, hB, hSc, hls1, hls2, hH⟩ := GlobalTheory.T.specialPrimeThreshold_numerics_along_family Fm x hx1 a
  have ht1 : 1 ≤ (Fm.D x a).R.t := by
    have := (Fm.D x a).R.rank_add_five_le; omega
  have htR : (0 : ℝ) ≤ (Fm.D x a).R.t := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_, fun h => absurd (hsS l h) (not_lt.2 hlS.le)⟩, ?_⟩
  · have : (7 : ℝ) < l := by linarith
    exact_mod_cast (show 5 ≤ l by exact_mod_cast (show (5 : ℝ) ≤ l by linarith))
  · have : ((Fm.D x a).R.t : ℝ) + 1 < l := by linarith
    exact_mod_cast this
  · intro h; rw [h] at hlS; linarith
  · intro h; rw [h] at hlS; linarith
  intro hexc j hj1 hjm n _ up τ
  have hfinL : ∀ c, (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.lowJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin (Fm.D x a).R.m => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) - ((Fm.D x a).hc (τ c)).b i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.lowT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  have hfinC : ∀ c, (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)).Finite := by
    intro c
    have h0 : (AdmissibleParameterJ.cloudJ (Fm.D x a) j (τ c)).Finite :=
      (Set.finite_range (fun i : Fin ((Fm.D x a).R.k - 1) => AdmissibleParameterJ.sz (Fm.D x a) j (τ c) + ((Fm.D x a).hc (τ c)).v i + AdmissibleParameterJ.c0 (Fm.D x a))).subset
        (by rintro q ⟨i, rfl⟩; exact ⟨i, rfl⟩)
    unfold AdmissibleParameterJ.cloudT
    split_ifs
    · exact h0
    · exact h0.preimage (Set.injOn_of_injective (fun p q h => by unfold AdmissibleParameterJ.refl at h; linarith))
  set Fl : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.lowT (Fm.D x a) (up c) j (τ c)) with hFl
  set Fc : ZMod n → Finset ℤ := fun c => GlobalTheory.PositionData.intPts (AdmissibleParameterJ.cloudT (Fm.D x a) (up c) j (τ c)) with hFc
  have hdat : ∀ c, ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a),
      (∀ z ∈ Fl c, |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
        2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
          |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
      (∀ z ∈ Fc c, W0 ≤ (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
        (if up c then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
          W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1) := by
    intro c
    obtain ⟨hlo, W0, hW0, hcl⟩ := GlobalTheory.T.lowJumps_and_cloud_in_windows_along_family Fm x hx1 a j hj1 hjm (up c) (τ c)
    refine ⟨W0, hW0, fun z hz => hlo z ((GlobalTheory.PositionData.mem_intPts (hfinL c) z).1 hz),
      fun z hz => hcl z ((GlobalTheory.PositionData.mem_intPts (hfinC c) z).1 hz)⟩
  set hh : ZMod n → ℕ := fun c => GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) with hhh
  have hhle : ∀ c, (hh c : ℝ) ≤ (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 := by
    intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, hW2⟩ := GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0
    have := GlobalTheory.T.shiftedJumpUpperBound_le_twist_bound (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 ht1 htη hB hSc hlo hcl hW1
    show ((GlobalTheory.PositionData.hS (up c) (Fm.D x a).R.t (Fl c) (Fc c) : ℕ) : ℝ) ≤ _
    linarith
  have hsg : ∀ c, (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) ≤ 2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) := by
    intro c
    have hl2 : 2 ≤ l := hl.two_le
    set W := (Fm.L x a).sc.b + (Fm.L x a).Sc + 2 * (Fm.L x a).etaSz + 3 with hW
    have hW0 : 0 ≤ W := le_trans (Nat.cast_nonneg _) (hhle c)
    have h1 := Formalism.IrreducibleCountingLemmas.TOP.carryFloorLeGeom n l hh ⌊W⌋₊ hl2 (fun c' => Nat.le_floor (hhle c')) c
    have h2 : ((⌊W⌋₊ : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ W / ((l : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right (Nat.floor_le hW0)
      have : (2 : ℝ) ≤ l := by exact_mod_cast hl2
      linarith
    have h3 := Formalism.IrreducibleCountingLemmas.TOP.geomRatioBound l (LevelStarExponents.lStar (Fm.L x a)) (Fm.L x a).sc.b W hW0 hls1 hlS hH
    have h4 : (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c : ℝ) = (Formalism.IrreducibleCountingLemmas.TOP.sg n l hh c : ℝ) := rfl
    rw [h4, ← mul_div_assoc]
    linarith
  refine ⟨hh, fun c => GlobalTheory.PositionData.wS (up c) (Fl c) (Fc c), fun c => GlobalTheory.PositionData.etaS (Fm.D x a).R.t (Fl c),
    up, fun c => GlobalTheory.PositionData.US (up c) (Fl c) (Fc c), ?_, ?_⟩
  · intro c
    obtain ⟨W0, hW0, hlo, hcl⟩ := hdat c
    obtain ⟨hW1, -⟩ := GlobalTheory.T.baseSize_bounds_along_family Fm x hx1 a W0 hW0
    have hex : ∀ m : ℤ, W0 + (-(Fm.L x a).etaSz - 2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) - 3) ≤ (m : ℝ) →
        (m : ℝ) ≤ W0 + ((Fm.L x a).Sc + (Fm.L x a).etaSz + (Fm.L x a).etaSz +
          2 * (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) : ℝ) + 4) → ¬ (l : ℤ) ∣ m :=
      fun m h1 h2 hd => hexc ⟨hl, hlS, W0, hW0, m, ⟨h1, h2⟩, hd⟩
    have hσP : Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus
      apply Int.le_floor.mpr
      rw [mul_div_assoc]; exact hsg c
    have hT1 : 2 * (Fm.L x a).etaSz + 8 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + 7 < (l : ℝ) := by linarith
    exact GlobalTheory.T.jump_position_conditions_at_letter l (Fm.D x a).R.t (up c) (Fl c) (Fc c) (Fm.L x a).etaSz (Fm.L x a).Sc
      ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) W0 (GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sgPlus (Fm.L x a)) (Formalism.MainNotions.tableLineDegreeTwo.sg n l hh c)
      ht1 htη hB hSc hlo hcl hW1 hex (hsg c) hσP hT1
  · intro c b
    rw [GlobalTheory.PositionData.count_US]
    have hm : b ∈ Fl c ∪ Fc c ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW (Fm.D x a) (up c) j (τ c) := by
      rw [Finset.mem_union, GlobalTheory.PositionData.mem_intPts (hfinL c), GlobalTheory.PositionData.mem_intPts (hfinC c)]
      unfold AdmissibleParameterJ.JW
      rw [Set.mem_union]; tauto
    rw [← hm]
    split_ifs <;> simp_all

end GlobalTheory.LocalPositionData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrincipalRoot
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLeft

theorem exists_principal_root {D : D7} (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) :
    ∃ e : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom e) := by
  obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hdet : ((matHom V γ).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      incA D γ₀.1.det := by
    rw [← GlobalTheory.DetRootRows.det_bc, h0]; rfl
  generalize γ₀.1.det = d at hdet
  have hc : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  have hn : star d * d = 1 := by
    have := det_conj_mul V γ
    apply GlobalTheory.DetRootRows.inclR_injective (F := D.host.F) (AF D.host.F)
    rw [map_mul, map_one, ← hc, ← hdet]
    exact this
  obtain ⟨e, he0, he⟩ : ∃ e : D.host.E, e ≠ 0 ∧ e = d * star e := by
    by_cases hd : d = -1
    · obtain ⟨a, ha⟩ := GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm
      refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
      rw [hd, star_sub, star_star]; ring
    · refine ⟨1 + d, fun h => hd (by linear_combination h), ?_⟩
      rw [star_add, star_one]; linear_combination -hn
  refine ⟨Units.mk0 e he0, ?_⟩
  unfold IsDetRoot
  rw [hdet]
  show incA D e = incA D d * cA D (incA D e)
  rw [hc, ← map_mul, ← he]

theorem muVal_left {D : D7} (V : HSp D) (χ : (AE D)ˣ →* Circle)
    (hE : ∀ x : D.host.Eˣ, χ (Units.map (incA D).toMonoidHom x) = 1) (mu : GA D V → ℂ) (hmu : MuVal V χ mu)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : mu (γ * h) = mu h := by
  obtain ⟨x, hx⟩ := hmu.1 h
  obtain ⟨e, he⟩ := exists_principal_root V γ hγ
  rw [hmu.2 _ _ (detRootMul_holds V γ h _ x he hx), hmu.2 h x hx, map_mul, hE e, one_mul]

theorem twist_left : ∀ (D : D7) (V : HSp D) (pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E)
    (δc : (AE D)ˣ →* Circle), IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) →
    ∀ γ ∈ GQ V, ∀ h : GA D V, dd (γ * h) = dd h := by
  intro D V pd k _ σ δ δc ht dd hdd γ hγ h
  have hE : ∀ x : D.host.Eˣ, δc (Units.map (incA D).toMonoidHom x) = 1 := ht.1.1.2
  rcases hdd with hm | hm
  · exact muVal_left V δc hE dd hm γ hγ h
  · exact muVal_left V δc⁻¹ (fun x => by rw [MonoidHom.inv_apply, hE x, inv_one]) dd hm γ hγ h

end GlobalTheory.TwistLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocyc
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases

section Gen1
variable {O : Type} [CommRing O]

def evOneQ (LL : Type) [Field LL] [Algebra O LL] : ((Fin 1 → LL) ⧸ stdG O LL 1) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL 1).mapQ (intO (O := O) LL) (LinearMap.proj (R := O) (φ := fun _ : Fin 1 => LL) 0) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u 0, rfl⟩)

variable {LL : Type} [Field LL] [Algebra O LL]

theorem evOneQ_mk (v : Fin 1 → LL) :
    evOneQ (O := O) LL (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v 0) := rfl

theorem evOneQ_mem {lam : O} {a : ℕ} {q : (Fin 1 → LL) ⧸ stdG O LL 1} (h : lam ^ a • q = 0) :
    evOneQ LL q ∈ Xq LL lam a := by
  show (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] _)) (evOneQ LL q) = 0
  rw [LinearMap.smul_apply, LinearMap.id_apply, ← map_smul, h, map_zero]

def oneO : ↥(intO (O := O) LL) := ⟨1, 1, map_one (algebraMap O LL)⟩

theorem iotaC_oneO (lam : O) (a : ℕ) (q : (Fin 1 → LL) ⧸ stdG O LL 1) (h : evOneQ LL q ∈ Xq LL lam a) :
    iotaC LL lam a (oneO ⊗ₜ ⟨evOneQ LL q, h⟩) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) (oneO ⊗ₜ (evOneQ LL (Submodule.Quotient.mk v))) = _
    rw [evOneQ_mk, iotaG_tmul]
    congr 1
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [constOne, oneO]

def oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) : ↥(latOne hinj ψ).T :=
  oneO

theorem actT_latOne_oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) (g : G) :
    actT (latOne hinj ψ) g (oneT hinj ψ) = ((ψ g : Oˣ) : O) • oneT hinj ψ := by
  apply Subtype.ext
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • (1 : LL) = ((ψ g : Oˣ) : O) • (1 : LL)
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

end Gen1

section Gen2
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem actTw_oneO (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (X : Type) [AddCommGroup X] [Module O X] (χ ψ : G →* Oˣ) (g : G) (x : X) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) X χ g (oneT hinj ψ ⊗ₜ x) = oneT hinj ψ ⊗ₜ ((((χ g)⁻¹ * ψ g : Oˣ) : O) • x) := by
  rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, actT_latOne_oneT, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, Units.val_mul, mul_smul]

theorem evOneQ_actD (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (g : G) (q : (Fin 1 → LL) ⧸ stdG O LL 1) :
    evOneQ LL (actD (stdLatG hinj N) g q) = N g 0 0 • evOneQ LL q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show evOneQ LL (Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g v)) = _
    rw [evOneQ_mk, evOneQ_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    simp [matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

end Gen2

section Gen3
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem liftC_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (χ ψ : G →* Oˣ) (hN : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = N g 0 0)
    (lam : O) (a : ℕ) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1) (hf : f ∈ divisibleCocycles (stdLatG hinj N))
    (htor : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (latOne hinj ψ) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaC LL lam a (z' g) = f g := by
  classical
  obtain ⟨hlc, hco⟩ := hf
  let F : ((Fin 1 → LL) ⧸ stdG O LL 1) → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a) :=
    fun q => if hq : lam ^ a • q = 0 then oneT hinj ψ ⊗ₜ ⟨evOneQ LL q, evOneQ_mem hq⟩ else 0
  refine ⟨fun g => oneT hinj ψ ⊗ₜ ⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩, ⟨?_, ?_⟩, ?_⟩
  · have hF : (fun g => oneT hinj ψ ⊗ₜ[O]
        (⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩ : ↥(Xq LL lam a))) = F ∘ f := by
      funext g
      simp only [F, Function.comp_apply, dif_pos (htor g)]
    rw [hF]
    exact hlc.comp F
  · intro g h
    beta_reduce
    rw [actTw_oneO, ← TensorProduct.tmul_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [hco g h, hN g]
    exact ((evOneQ LL).map_add _ _).trans (congrArg (evOneQ LL (f g) + ·) (evOneQ_actD hinj N g (f h)))
  · intro g
    exact iotaC_oneO lam a (f g) _

end Gen3

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locOC_chiRatO_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 =
      ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, Br.iota, mapM, chiRatO, twistM]

theorem chiT_one_eq_theta (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

theorem chiT_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = locOC C (chiRatO D.nd i c) g 0 0 := by
  rw [locOC_chiRatO_apply, chiT_one_eq_theta]
  congr 1
  simp only [chiT, MonoidHom.mul_apply]
  rw [mul_comm, mul_assoc, mul_inv_cancel, mul_one]

end AtW

theorem liftC_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  intro D i w hw C lam _ θ c a f hf htor
  exact liftC_gen Subtype.val_injective (locOC C (chiRatO D.nd i c)) (chiT C θ 1) (chiT C θ c) (chiT_ratio C θ c)
    lam a f hf htor

end GlobalTheory.UseLoc.Cases

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtraBoundOfTwistingEigenFacts
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.ExtraFromFacts

theorem main : Hypotheses₂ → ∃ (C : ℝ) (CT : ℕ), 0 ≤ C ∧ ∀ (D : D7) (nch : NChoice D), GlobalTheory.NFacts.Facts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → Extra D C CT := by
  intro hP
  obtain ⟨CT, hCT⟩ := GlobalTheory.T.bound_of_twisting_eigen_series_facts hP
  refine ⟨8 * (CT : ℝ), CT, by positivity, ?_⟩
  intro D nch hf h
  refine ⟨?_, hCT D nch hf h⟩
  obtain ⟨hchi, ⟨Q, hDZ, hE⟩, hine, hser⟩ := h
  have hS := GlobalTheory.T.steps_of_artin_reciprocity hP.artin
  exact GlobalTheory.T.joint_condition_of_eigen_central_series D Q hE (hS.2.1 hS.1 D Q) hser hf.Conclusion1.1 hf.what₂.a.tieLab
    hf.adm.1.1.1 hf.adm.1.1.2.2.1 hf.adm.1.1.2.2.2.2.2.2

end GlobalTheory.ExtraFromFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModInt
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem finite_Xq {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)) (hlam : Irreducible lam) (a : ℕ) :
    Finite ↥(Xq ↥LL.1 lam a) := by
  classical
  haveI := GlobalTheory.FullCharpoly.hasFiniteQuotients_OL LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hne : lam ^ a ≠ 0 := pow_ne_zero _ hlam.ne_zero
  have hK : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) ≠ 0 := by
    intro h; exact hne (hinj (by rw [h, map_zero]))
  haveI : Finite (↥(OL LL) ⧸ Ideal.span {lam ^ a}) := Ring.HasFiniteQuotients.finiteQuotient (by
    rwa [Ne, Ideal.span_singleton_eq_bot])
  have hex : ∀ x : ↥(Xq ↥LL.1 lam a), ∃ c : ↥(OL LL), ∃ s : ↥LL.1,
      Submodule.Quotient.mk (p := intO (O := ↥(OL LL)) ↥LL.1) s = x.1 ∧ algebraMap ↥(OL LL) ↥LL.1 c = lam ^ a • s := by
    intro x
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx := x.2
    simp only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx
    rw [← hs, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, s, hs, hc⟩
  let f : ↥(Xq ↥LL.1 lam a) → ↥(OL LL) ⧸ Ideal.span {lam ^ a} := fun x => Ideal.Quotient.mk _ (hex x).choose
  refine Finite.of_injective f ?_
  intro x y hxy
  obtain ⟨s, hs, hc⟩ := (hex x).choose_spec
  obtain ⟨t, ht, hd⟩ := (hex y).choose_spec
  have h1 := hxy
  simp only [f, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨d, hd'⟩ := h1
  apply Subtype.ext
  rw [← hs, ← ht, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  refine ⟨d, ?_⟩
  have h2 : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * (s - t) = algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * algebraMap ↥(OL LL) ↥LL.1 d := by
    rw [← map_mul, mul_comm (lam ^ a) d, hd', map_sub, hc, hd, Algebra.smul_def, Algebra.smul_def, mul_sub]
  have := mul_left_cancel₀ hK h2
  simp only [Algebra.linearMap_apply]
  exact this.symm

end GlobalTheory.UseLoc.Cases
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialCompatible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.TieInePolyPin

theorem inePol_eq_wdAt : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), Continuous (fun g => ((r g : GL _ _) : Matrix (Fin m) (Fin m) (D.nd.O i))) → GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) r) w) σ = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol σ := by
  intro hL D P i w hw m r hc hpst σ hσ
  have hc' : Continuous (fun g => ((GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w g : GL _ _) : Matrix (Fin m) (Fin m) (Om (D.nd.l i)))) :=
    ((hc.matrix_map (GlobalTheory.T.continuous_iotaOQ' D.nd D.naut i)).comp continuous_subtype_val)
  rw [(P.wdOf i m (mapRep (iotaOQ D.nd D.naut i) r) w).1, P.T.inePol w _ σ hσ]
  obtain ⟨LL, Bw, hj, e2⟩ := P.wd.above (D.nd.l i) (D.naut.iotaQC i) (mapRep (iotaOQ D.nd D.naut i) r) w hw
  rw [e2]
  refine congrArg (fun x => GlobalTheory.WeilDeligne.WD.inePol x σ) ?_
  exact GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩
    (D.naut.iotaQC i) D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ Bw (D.nbr i w hw) (D.nd.plOm.2 w) hj (D.nbr_ind i w hw) m _ hc'
    (GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ D.host.E D.nd.Om (D.nd.plOm.1 w) _ _
      (D.nbr i w hw) Bw (D.nbr_ind i w hw) hj m _ hc' hpst) hpst

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), GlobalTheory.Pass.TieInePoly D := by
  intro hL D P i w hw K' h hN hF hS m r hc hpot σ hσ p hp d hd
  exact GlobalTheory.T.inertiaPolynomial_kills_potentiallyCrystalline_module D i w hw K' h hN hF hS m r hc hpot σ hσ p
    (hp.trans (inePol_eq_wdAt hL D P i w hw m r hc (GlobalTheory.T.potSemistable_of_potCrystalline_decompositionGroup D i w hw K' h hN hF hS m r hc hpot) σ hσ)) d hd

end GlobalTheory.TieInePolyPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgro
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {G : Type} [Group G] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]

theorem actT_latOne (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (g : G) :
    actT (latOne (LL := LL) hinj ψ) g = ((ψ g : Oˣ) : O) • LinearMap.id := by
  ext t
  change Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ) g (t : LL) = (((ψ g : Oˣ) : O) • t : LL)
  simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.smul_def]

theorem actTw_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ) (X : Type)
    [AddCommGroup X] [Module O X] (g : G) :
    tableLineDegreeTwo.actTw (latOne (LL := LL) hinj ψ) X ψ g = LinearMap.id := by
  rw [tableLineDegreeTwo.actTw, actT_latOne, LinearMap.rTensor_smul, LinearMap.rTensor_id, smul_smul]
  simp

theorem eq_zero_of_isUnr_latOne [TopologicalSpace G] (hinj : Function.Injective (algebraMap O LL)) (ψ : G →* Oˣ)
    (X : Type) [AddCommGroup X] [Module O X] (I : Subgroup G) (z : G → ↥(latOne (LL := LL) hinj ψ).T ⊗[O] X)
    (h : tableLineDegreeTwo.IsUnr (latOne (LL := LL) hinj ψ) X ψ I z) : ∀ g ∈ I, z g = 0 := by
  obtain ⟨m, hm⟩ := h
  intro g hg
  rw [hm g hg, actTw_latOne, LinearMap.id_apply, sub_self]

theorem mem_Z1urD_of_eq_zero {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (I : Subgroup G) (c : G → V ⧸ L.T)
    (h : ∀ g ∈ I, c g = 0) : c ∈ Z1urD L I :=
  ⟨0, fun g hg => by rw [h g hg, map_zero, sub_zero]⟩

end Gen

end GlobalTheory.UseLoc.Cases

theorem GlobalTheory.UseLoc.Cases.readU_unr : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  intro D i w hw C lam θ a I z' h
  exact GlobalTheory.UseLoc.Cases.mem_Z1urD_of_eq_zero _ I _ (fun g hg =>
    (congrArg (iotaC ↥C.LL.1 lam a) (GlobalTheory.UseLoc.Cases.eq_zero_of_isUnr_latOne _ _ _ I z' h g hg)).trans (map_zero _))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLabelDeterminantStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_label_determinant : ∀ (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), LabAll D P.T → ∀ (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → labAt hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  first | exact @GlobalTheory.LabConjPlace.main | exact GlobalTheory.LabConjPlace.main | (intros; apply GlobalTheory.LabConjPlace.main <;> assumption)
end

