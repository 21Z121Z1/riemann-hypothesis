import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0089
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.Columns.BaseHost
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctOfSsOfAbsIrrOfMapRepDistinctStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrDistinct_of_isSS_absIrr_mapRep_nonIso : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) → (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep f ρ) W₁ W₂) → AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  first | exact @GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | exact GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | (intros; apply GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AfIsoEqZeroIffStatement
section
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.afIso_ringEquiv_eq_zero_iff : ∀ (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (s : E ≃+* E') (φ : AfE F E ≃+* AfE F' E'), (∀ x : E, φ (x ⊗ₜ[F] 1) = s x ⊗ₜ[F'] 1) → (∀ y, φ y ∈ RInt F' E' ↔ y ∈ RInt F E) → ∀ y ∈ RInt F E, ∀ P : HeightOneSpectrum (𝓞 E), (GlobalTheory.Mem.Col2.afIso F' E' (φ y) (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P) = 0 ↔ GlobalTheory.Mem.Col2.afIso F E y P = 0) := by
  first | exact @GlobalTheory.AfeLocTr.afIso_eq_zero_iff | exact GlobalTheory.AfeLocTr.afIso_eq_zero_iff | (intros; apply GlobalTheory.AfeLocTr.afIso_eq_zero_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaModelCoefficientsInvertLStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_model_coefficients_invert_l : Formalism.L2.KerInert.BeCob.BeCoef := by
  first | exact @GlobalTheory.BeCoefficients.beCoef | exact GlobalTheory.BeCoefficients.beCoef | (intros; apply GlobalTheory.BeCoefficients.beCoef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
section
open Formalism.L2.Col

namespace GlobalTheory.TopLaw

theorem blkDet_eq_dB : ∀ {κ : Type} [CommRing κ] {n : ℕ} (β : ℕ → ℕ) (c s t : ℕ), s + t ≤ n → (∀ i, i < n → (β i = c ↔ s ≤ i ∧ i < s + t)) → ∀ (M : btG n κ β) (A : ℕ → ℕ → κ), (∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) → ((blkDet n κ β c M : κˣ) : κ) = GlobalTheory.DatumLaw.dB A s t := by
  intro κ _ n β c s t hn hβ M A hA
  rw [blkDet_val]
  unfold GlobalTheory.DatumLaw.dB
  let e : Fin t ≃ {i : Fin n // β i.1 = c} :=
    { toFun := fun u => ⟨⟨s + u.1, by have := u.2; omega⟩, (hβ _ (by have := u.2; omega)).2 ⟨by simp, by have := u.2; simp⟩⟩
      invFun := fun i => ⟨i.1.1 - s, by have := (hβ _ i.1.2).1 i.2; omega⟩
      left_inv := fun u => Fin.ext (by simp)
      right_inv := fun i => Subtype.ext (Fin.ext (by have := (hβ _ i.1.2).1 i.2; simp only; omega)) }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext u v
  exact (hA (e u).1 (e v).1).symm

end GlobalTheory.TopLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyReductionGoodPrimeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_reduction_good_prime : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.IotaRed D → GlobalTheory.RowTie.RowRepAtG D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩; Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) : Matrix (Fin D.R.r) (Fin D.R.r) _) = ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod := by
  first | exact @GlobalTheory.ResidualTame.charpoly_tameGen | exact GlobalTheory.ResidualTame.charpoly_tameGen | (intros; apply GlobalTheory.ResidualTame.charpoly_tameGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoboundaryIntegralLawRespectsSimeqStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_integral_law_respects_simeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  first | exact @GlobalTheory.CobSimeqProof.cobSimeq | exact GlobalTheory.CobSimeqProof.cobSimeq | (intros; apply GlobalTheory.CobSimeqProof.cobSimeq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffsWpSubst
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

open MvPowerSeries Formalism.MainNotions.GL3Theta

theorem coeffsWp_mul {τ : Type} {p : ℕ} [Fact p.Prime] {f g : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (hg : ∀ m, coeff m g ∈ Wp p) : ∀ m, coeff m (f * g) ∈ Wp p := by
  intro m
  rw [coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)

theorem coeffsWp_one {τ : Type} {p : ℕ} [Fact p.Prime] : ∀ m, coeff m (1 : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem coeffsWp_pow {τ : Type} {p : ℕ} [Fact p.Prime] {f : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (k : ℕ) : ∀ m, coeff m (f ^ k) ∈ Wp p := by
  induction k with
  | zero => simpa using coeffsWp_one
  | succ k ih => rw [pow_succ]; exact coeffsWp_mul ih hf

theorem coeffsWp_subst {σ τ : Type} {p : ℕ} [Fact p.Prime] {a : σ → MvPowerSeries τ ℂ_[p]} (ha : HasSubst a)
    (hA : ∀ i m, coeff m (a i) ∈ Wp p) {f : MvPowerSeries σ ℂ_[p]} (hf : ∀ m, coeff m f ∈ Wp p) :
    ∀ m, coeff m (subst a f) ∈ Wp p := by
  intro e
  rw [coeff_subst ha]
  refine finsum_induction (fun w => w ∈ Wp p) (Subring.zero_mem _) (fun x y hx hy => Subring.add_mem _ hx hy) ?_
  intro d
  refine Subring.mul_mem _ (hf d) ?_
  have hP : ∀ m, coeff m (d.prod fun s k => a s ^ k) ∈ Wp p := by
    unfold Finsupp.prod
    induction d.support using Finset.induction_on with
    | empty => simpa using coeffsWp_one
    | insert i S hi ih => rw [Finset.prod_insert hi]; exact coeffsWp_mul (coeffsWp_pow (hA i) _) ih
  exact hP e

theorem coeffsWp_X {τ : Type} {p : ℕ} [Fact p.Prime] (t : τ) : ∀ m, coeff m (X t : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem hasSubst_copy {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) := by
  have hinj : Function.Injective (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := by
    intro s t h
    simpa using h
  haveI : Filter.TendstoCofinite (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := ⟨hinj.tendsto_cofinite⟩
  exact HasSubst.X_comp (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1))

theorem xiE_props {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p])
    (hx : ∀ r, IntegralW (x r) ∧ constantCoeff (x r) = 0) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) :
    constantCoeff (xiE x i) = 0 ∧ ∀ m, coeff m (xiE x i) ∈ Wp p := by
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩

theorem xiE_integral : ∀ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (xiE x i) = 0) ∧ ∀ F : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p), IntS p F → ∀ m, ‖MvPowerSeries.coeff m (MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F))‖ ≤ 1 := by
  intro p _ n' r0 r1 x hx
  have hP := xiE_props (r0 := r0) (r1 := r1) x hx
  refine ⟨fun i => (hP i).1, ?_⟩
  intro F hF m
  obtain ⟨g, rfl⟩ := hF
  have hs : HasSubst (xiE x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → _) :=
    hasSubst_of_constantCoeff_zero fun i => (hP i).1
  have hG : ∀ d, coeff d (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (MvPowerSeries.map (algebraMap (FormalGroupSystem.WW p) (FormalGroupSystem.K0 p)) g)) ∈ Wp p := by
    intro d
    rw [coeff_map, coeff_map]
    rw [Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
    exact Formalism.L2.G.Pend.wToC_mem_Wp p _
  exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (coeffsWp_subst hs (fun i => (hP i).2) hG m)

end GlobalTheory.OnePlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnField_ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok → ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  first | exact @GlobalTheory.ColumnField.ramificationIdxIn_eq_one | exact GlobalTheory.ColumnField.ramificationIdxIn_eq_one | (intros; apply GlobalTheory.ColumnField.ramificationIdxIn_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffBivariateSeriesSubstPair
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

noncomputable section

namespace GlobalTheory.OnePlacePairs

open MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expS_zero {κ : Type} : product_zeroth_first_parts.expS ℂ_[p] (0 : MvPowerSeries κ ℂ_[p]) = 1 := by
  have h := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (k := ℂ_[p]) (a := (0 : MvPowerSeries κ ℂ_[p])) (b := 0)
    (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries κ ℂ_[p]) (PowerSeries.exp ℂ_[p])) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp (by simp)]
    exact isUnit_one
  unfold product_zeroth_first_parts.expS
  exact hu.mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem expS_add {κ : Type} {f g : MvPowerSeries κ ℂ_[p]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (f + g) = product_zeroth_first_parts.expS ℂ_[p] f * product_zeroth_first_parts.expS ℂ_[p] g :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

theorem expS_sum {κ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries κ ℂ_[p]) (hf : ∀ i, constantCoeff (f i) = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (∑ i ∈ s, f i) = ∏ i ∈ s, product_zeroth_first_parts.expS ℂ_[p] (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [expS_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, expS_add (hf i) (by rw [map_sum]; exact Finset.sum_eq_zero fun j _ => hf j), ih]

theorem padicExpSeries_doubleSum {κ α β : Type} [Fintype α] [Fintype β] (f : α → β → MvPowerSeries κ ℂ_[p])
    (hf : ∀ a b, constantCoeff (f a b) = 0) :
    product_zeroth_first_parts.expS ℂ_[p] (∑ a, ∑ b, f a b) = ∏ a, ∏ b, product_zeroth_first_parts.expS ℂ_[p] (f a b) := by
  rw [expS_sum _ _ (fun a => by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hf a b)]
  exact Finset.prod_congr rfl fun a _ => expS_sum _ _ (hf a)

theorem cc_logF : PowerSeries.constantCoeff (Formalism.MainNotions.GL3Theta.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.MainNotions.GL3Theta.logF, PowerSeries.coeff_mk]
  simp

theorem cc_plog {κ : Type} {u : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) :
    constantCoeff (PowerSeries.subst u (Formalism.MainNotions.GL3Theta.logF p)) = 0 := by
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hu, cc_logF]

theorem constantCoeff_bivariateSeriesSubstPair {κ : Type} {b0 : MvPowerSeries (Fin 2) ℂ_[p]} (hb0 : constantCoeff b0 = 0)
    {u v : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    constantCoeff (GlobalTheory.ThBe0.at2 b0 u v) = 0 := by
  have h : ∀ i : Fin 2, constantCoeff (if i = 0 then u else v) = 0 := fun i => by split_ifs <;> assumption
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hb0

theorem subst_powerSeriesEvalTwoGroups {κ κ' : Type} {φ : κ → MvPowerSeries κ' ℂ_[p]} (hφ : HasSubst φ) (b0 : MvPowerSeries (Fin 2) ℂ_[p])
    {u v : MvPowerSeries κ ℂ_[p]} (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    subst φ (GlobalTheory.ThBe0.at2 b0 u v) = GlobalTheory.ThBe0.at2 b0 (subst φ u) (subst φ v) := by
  have h : ∀ i : Fin 2, constantCoeff (if i = 0 then u else v) = 0 := fun i => by split_ifs <;> assumption
  unfold GlobalTheory.ThBe0.at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h) hφ]
  congr 1
  funext i
  split_ifs <;> rfl

variable {n' : ℕ} [NeZero n']

theorem hasSubst_pair {r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem cc_jet {r0 r1 : ℕ} (v : ZMod n' × Fin r0 × Fin r1) : constantCoeff (jetLogG p n' v) = 0 := by
  rw [← GlobalTheory.BiextInhab.bridge p n' v.2 v.1]
  exact GlobalTheory.BeProps.constantCoeff_laAt _ _

theorem hasSubst_jet' {r0 r1 : ℕ} : HasSubst (jetLogG p n' (β := Fin r0 × Fin r1)) :=
  hasSubst_of_constantCoeff_zero cc_jet

theorem pair_eq {r0 r1 : ℕ} (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p])
    (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (V : MvPowerSeries (ZMod n') ℂ_[p])
    (hb0 : constantCoeff b0 = 0) (hbv : constantCoeff bv = 0) (hx : ∀ r, constantCoeff (x r) = 0)
    (H : product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
      (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(subst (GlobalTheory.ThStr.laS p n') bv)))
    (a : Fin r0) (b : Fin r1) :
    product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0
                               (PowerSeries.subst (xiE x (Sum.inl ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p))
                               (PowerSeries.subst (xiE x (Sum.inr ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p)))) =
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V *
        product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
  have hψ := hasSubst_pair (p := p) (n' := n') a b
  have hcL : constantCoeff (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
      (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = 0 := by
    rw [map_neg, map_sum, Finset.sum_eq_zero fun r _ => constantCoeff_bivariateSeriesSubstPair hb0 (cc_plog (hx _)) (cc_plog (hx _)), neg_zero]
  have hLa : HasSubst (GlobalTheory.ThStr.laS p n') := hasSubst_of_constantCoeff_zero GlobalTheory.BeProps.constantCoeff_laS
  have hcR : constantCoeff (-(subst (GlobalTheory.ThStr.laS p n') bv)) = 0 := by
    rw [map_neg, constantCoeff_subst_eq_zero hLa GlobalTheory.BeProps.constantCoeff_laS hbv, neg_zero]
  have e1 : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
      (product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p))))) =
      product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0
        (PowerSeries.subst (xiE x (Sum.inl ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p))
        (PowerSeries.subst (xiE x (Sum.inr ((r, a, b) : Eidx n' r0 r1))) (Formalism.MainNotions.GL3Theta.logF p)))) := by
    rw [product_zeroth_first_parts.expS, product_zeroth_first_parts.expS, GlobalTheory.BeProps.subst_psubst hψ hcL, ← substAlgHom_apply hψ, map_neg, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [substAlgHom_apply, subst_powerSeriesEvalTwoGroups hψ b0 (cc_plog (hx _)) (cc_plog (hx _)),
      GlobalTheory.BeProps.subst_psubst hψ (hx _), GlobalTheory.BeProps.subst_psubst hψ (hx _)]
    rfl
  have e2 : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
      (V * product_zeroth_first_parts.expS ℂ_[p] (-(subst (GlobalTheory.ThStr.laS p n') bv))) =
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V *
        product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
    have hn : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]))
        (-(subst (GlobalTheory.ThStr.laS p n') bv)) = -(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv) := by
      rw [← substAlgHom_apply hψ, map_neg, substAlgHom_apply, subst_comp_subst_apply hLa hψ]
      congr 2
      funext s
      exact GlobalTheory.BiextInhab.bridge p n' (a, b) s
    rw [product_zeroth_first_parts.expS, product_zeroth_first_parts.expS, ← substAlgHom_apply hψ, map_mul]
    simp only [substAlgHom_apply]
    rw [GlobalTheory.BeProps.subst_psubst hψ hcR, hn]
  rw [← e1, ← e2, H]

theorem integralW_pair {r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) {V : MvPowerSeries (ZMod n') ℂ_[p]}
    (hV : Formalism.MainNotions.GL3Theta.IntegralW V) :
    Formalism.MainNotions.GL3Theta.IntegralW (subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V) := by
  let e : ZMod n' ↪ ZMod n' × Fin r0 × Fin r1 := ⟨fun s => (s, a, b), fun x y h => (Prod.mk.inj h).1⟩
  have he : subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V =
      rename e V := by
    rw [rename_eq_subst]; rfl
  rw [he]
  intro m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (e : ZMod n' → ZMod n' × Fin r0 × Fin r1))
  · obtain ⟨n, rfl⟩ := hm
    rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
    exact hV n
  · rw [coeff_rename_eq_zero _ _ hm]
    exact zero_mem _

theorem cc_xiE {r0 r1 : ℕ} {x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]}
    (hx : ∀ r, constantCoeff (x r) = 0) (e : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : constantCoeff (xiE x e) = 0 := by
  rcases e with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) (hx _)
  · exact constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) (hx _)

theorem sum_reorder {r0 r1 : ℕ} {M : Type*} [AddCommMonoid M] (f : Eidx n' r0 r1 → M) :
    ∑ e, f e = ∑ a : Fin r0, ∑ b : Fin r1, ∑ r : Fin (n' / 2), f (r, a, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]

theorem neg_doubleSum_eq_doubleSum_neg {α β M : Type*} [Fintype α] [Fintype β] [AddCommGroup M] (g : α → β → M) :
    -(∑ a, ∑ b, g a b) = ∑ a, ∑ b, -g a b := by
  simp [Finset.sum_neg_distrib]

theorem rhs_eq {r0 r1 : ℕ} (bv : MvPowerSeries (ZMod n') ℂ_[p]) (hbv : constantCoeff bv = 0) :
    subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) =
      ∏ a : Fin r0, ∏ b : Fin r1, product_zeroth_first_parts.expS ℂ_[p] (-(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv)) := by
  have hJ := hasSubst_jet' (p := p) (n' := n') (r0 := r0) (r1 := r1)
  have hc : constantCoeff (-(∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) = 0 := by
    rw [map_neg, map_sum, Finset.sum_eq_zero fun a _ => ?_, neg_zero]
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => constantCoeff_subst_eq_zero (hasSubst_pair a b) (fun _ => constantCoeff_X _) hbv
  have e : subst (jetLogG p n' (β := Fin r0 × Fin r1)) (-(∑ a : Fin r0, ∑ b : Fin r1,
      subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) =
      ∑ a : Fin r0, ∑ b : Fin r1, -(subst (fun s : ZMod n' => jetLogG p n' (s, a, b)) bv) := by
    rw [← substAlgHom_apply hJ, map_neg, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [substAlgHom_apply, subst_comp_subst_apply (hasSubst_pair a b) hJ]
    congr 2
    funext s
    rw [subst_X hJ]
  rw [neg_one_smul, product_zeroth_first_parts.expS, GlobalTheory.BeProps.subst_psubst hJ hc, e]
  exact padicExpSeries_doubleSum _ fun a b => by
    rw [map_neg, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun s => cc_jet _) (fun s => cc_jet _) hbv,
      neg_zero]

end GlobalTheory.OnePlacePairs

namespace GlobalTheory.OnePlacePairs

open MvPowerSeries

theorem pairs_all : ∀ {p : ℕ} [Fact p.Prime] {n' : ℕ} [NeZero n'] (b0 : MvPowerSeries (Fin 2) ℂ_[p]) (bv : MvPowerSeries (ZMod n') ℂ_[p]) (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) (V : MvPowerSeries (ZMod n') ℂ_[p]), MvPowerSeries.constantCoeff b0 = 0 → MvPowerSeries.constantCoeff bv = 0 → (∀ r, MvPowerSeries.constantCoeff (x r) = 0) → Formalism.MainNotions.GL3Theta.IntegralW V → product_zeroth_first_parts.expS ℂ_[p] (-(∑ r : Fin (n' / 2), GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (x (Sum.inl r)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (x (Sum.inr r)) (Formalism.MainNotions.GL3Theta.logF p)))) = V * product_zeroth_first_parts.expS ℂ_[p] (-(MvPowerSeries.subst (GlobalTheory.ThStr.laS p n') bv)) → ∀ (r0 r1 : ℕ), ∃ U2 : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U2‖ ≤ 1) ∧ product_zeroth_first_parts.expS ℂ_[p] (-(∑ e : Eidx n' r0 r1, GlobalTheory.ThBe0.at2 b0 (PowerSeries.subst (xiE x (Sum.inl e)) (Formalism.MainNotions.GL3Theta.logF p)) (PowerSeries.subst (xiE x (Sum.inr e)) (Formalism.MainNotions.GL3Theta.logF p)))) = U2 * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  intro p _ n' _ b0 bv x V hb0 hbv hx hV H r0 r1
  refine ⟨∏ a : Fin r0, ∏ b : Fin r1,
    subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V, fun m => ?_, ?_⟩
  · have hmem : (∏ a : Fin r0, ∏ b : Fin r1,
        subst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) V) ∈
        GlobalTheory.BiextInhab.serW p (ZMod n' × Fin r0 × Fin r1) :=
      Subring.prod_mem _ fun a _ => Subring.prod_mem _ fun b _ => GlobalTheory.BiextInhab.mem_serW.2 (integralW_pair a b hV)
    exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (GlobalTheory.BiextInhab.mem_serW.1 hmem m)
  · rw [rhs_eq bv hbv, ← Finset.prod_mul_distrib]
    simp only [← Finset.prod_mul_distrib]
    rw [sum_reorder, neg_doubleSum_eq_doubleSum_neg, padicExpSeries_doubleSum _ fun a b => by
      rw [map_neg, map_sum, Finset.sum_eq_zero fun r _ => constantCoeff_bivariateSeriesSubstPair hb0 (cc_plog (cc_xiE hx _)) (cc_plog (cc_xiE hx _)),
        neg_zero]]
    exact Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => pair_eq b0 bv x V hb0 hbv hx H a b

end GlobalTheory.OnePlacePairs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

namespace GlobalTheory.DetFields

open GlobalTheory.Mem.Col2.JetEx.VacEqPf

theorem iE_det {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    s.iE ((LinearEquiv.det γ : X.Eˣ) : X.E) = (matOf s γ).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  rw [show s.iE (LinearMap.toMatrix' (γ : Sp X.E n →ₗ[X.E] Sp X.E n)).det = _ from
    RingHom.map_det (s.iE : X.E →+* D.host.E) _]
  congr 1

theorem det_of_stab : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  intro D X s χ hok hχ n N' hL γ hγ
  have hd := iE_det s γ.1
  have hSD : Formalism.MainNotions.StandardLatticesGL3.SD D (s.lat N') := hL
  have hfg : (s.lat N').FG := hL.1
  have hsp : Submodule.span D.host.E ((s.lat N' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := hL.2.1
  have hU := matOf_unitary s hok γ
  set M := matOf s γ.1 with hM

  have hMM : GlobalTheory.RatEqui.adj D M * M = 1 ∧ M * GlobalTheory.RatEqui.adj D M = 1 := by
    letI := D.host.cmStar
    have e : star M = GlobalTheory.RatEqui.adj D M := by
      ext i j
      simp [GlobalTheory.RatEqui.adj, Matrix.star_apply, star_conj]
    rw [← e]
    exact ⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
  have hadj : M * GlobalTheory.RatEqui.adj D M = 1 := hMM.2

  have hs : ∀ v, v ∈ s.lat N' ↔ M.mulVec v ∈ s.lat N' := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := (mem_lat s N' v).1 hv
      refine (mem_lat s N' _).2 ⟨γ.1 x, ?_, (matOf_mulVec s γ.1 x).symm⟩
      rw [← hγ]
      exact ⟨x, hx, rfl⟩
    · intro hv
      obtain ⟨y, hy, hyv⟩ := (mem_lat s N' _).1 hv
      rw [← hγ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : M.mulVec (vec s x) = M.mulVec v := by
        rw [← hyv]
        exact matOf_mulVec s γ.1 x
      have hinj : vec s x = v := by
        have := congrArg (fun w => (GlobalTheory.RatEqui.adj D M).mulVec w) hx'
        simpa only [Matrix.mulVec_mulVec, hMM.1, Matrix.one_mulVec] using this
      rw [← hinj]
      exact (mem_lat s N' _).2 ⟨x, hx, rfl⟩

  have hdet : M.det * D.host.conj M.det = 1 := by
    have h1 : (GlobalTheory.RatEqui.adj D M).det = D.host.conj M.det := by
      unfold GlobalTheory.RatEqui.adj
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm
    rw [← h1, ← Matrix.det_mul, hMM.2, Matrix.det_one]
  refine ⟨?_, ?_, ?_⟩
  · apply s.iE.injective
    rw [map_mul, hok.2, hd, map_one]
    exact hdet
  · have i1 := GlobalTheory.DetStab.isIntegral_det_of_stable (s.lat N') hfg hsp M fun v hv => (hs v).1 hv
    have i2 : IsIntegral ℤ M.det := isIntegral_trans (R := ℤ) _ i1
    have i3 := map_isIntegral_int s.iE.symm.toRingHom i2
    rw [← hd] at i3
    simpa using i3
  · rw [hd]
    exact GlobalTheory.DetStab.prod_emb_det_eq_one D χ hχ n (s.lat N') hSD M hadj hs

end GlobalTheory.DetFields
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteExtAbsIrrSubStatement
section
open Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr : ∀ {K Γ ι : Type} [Field K] [Group Γ] [Finite ι] {a : ℕ} (ρ : ι → (Γ →* GL (Fin a) K)), (∀ j, IsSSRep (mapRep (algebraMap K (AlgebraicClosure K)) (ρ j))) → ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K'), ∀ j W, IsIrrSub (mapRep (algebraMap K K') (ρ j)) W → AbsIrrSub (mapRep (algebraMap K K') (ρ j)) W := by
  first | exact @GlobalTheory.SplitField.exists_finite_ext_absIrrSub | exact GlobalTheory.SplitField.exists_finite_ext_absIrrSub | (intros; apply GlobalTheory.SplitField.exists_finite_ext_absIrrSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeriesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_orbit_series : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (σ : MaximalUnramifiedExtension Lc.l →+* MaximalUnramifiedExtension Lc.l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension Lc.l)) (om oms : Fin (Lc.d / 2) → MaximalUnramifiedExtension Lc.l) (ζ : MaximalUnramifiedExtension Lc.l), BeData Lc.l Lc.d σ F be0 om oms ζ → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) (beOf Lc.l Lc.d σ be0 om oms ζ) → ∃ U0 : MvPowerSeries (Bool × Fin (Lc.d / 2) × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l], Formalism.DworkPowerSeriesWeights.Integral U0 ∧ (MvPowerSeries.subst (fun v : ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1 => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l])) Lc.Th : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l]) = thetaInZ (d := Lc.d) Lc.l (MaximalUnramifiedExtension Lc.l).subtype σ om oms (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension Lc.l).subtype be0))) * U0) := by
  first | exact @GlobalTheory.KerStd.integral_cofactor_converse | exact GlobalTheory.KerStd.integral_cofactor_converse | (intros; apply GlobalTheory.KerStd.integral_cofactor_converse <;> assumption)
end

