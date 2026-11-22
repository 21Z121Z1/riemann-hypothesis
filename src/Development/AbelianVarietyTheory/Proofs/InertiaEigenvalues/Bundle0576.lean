import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0200
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0564
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgIdentityProdOfUnitResultant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLinesOfLatticeAtLevels
section
noncomputable section

namespace GlobalTheory.SenLines.AllRoots

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.SenLines TensorProduct

theorem zeta_isPrimitiveRoot {l : ℕ} [Fact l.Prime] (P : LocPrime l) {s : ℕ} (hs : 1 ≤ s) :
    IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
    rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem exists_isPt {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ (l ^ s)) :
    ∃ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim := zeta_isPrimitiveRoot P hs
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos s).ne'⟩
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  have hζ' : IsPrimitiveRoot (ζ : Om l) (l ^ s) := hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  obtain ⟨a, -, ha⟩ := (hprim.map_of_injective (f := Φ) Φ.injective).eq_pow_of_pow_eq_one hζ'.pow_eq_one
  rw [← map_pow] at ha
  have hpa : IsPrimitiveRoot (P.ζQ s ^ a) (l ^ s) :=
    IsPrimitiveRoot.of_map_of_injective (f := Φ) (ha ▸ hζ') Φ.injective
  have hconj : IsConjRoot ↥(K0 K) (P.ζQ s ^ a) (P.ζQ s) := by
    unfold IsConjRoot
    rw [GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs _ hprim, GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs _ hpa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := (Φ.comp (σ.restrictScalars ℚ_[l]).toAlgHom).comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (σ (y : Om l)) := fun _ => rfl
  refine ⟨τ, fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩
  · rw [hτ, hxy, show σ (x : Om l) = x from σ.commutes x, hΦ]
  · rw [hτ, hy, hσ, ha]

theorem linesAt_of_latticeAtLevels {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} {C : LocCmpT l P AI H E} (hT : LocTied l P AI)
    (h4 : GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.LatticeAtLevels l P AI H E C) {K LL : FinExt l} (hA : CaseA K LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ)
    (hc : CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ U) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) : LinesAt (H.W K 1 LL hA.2.2) T i ζ (U i) := by
  obtain ⟨τ, hpt⟩ := exists_isPt H hA.2.2 i ζ (by rwa [pow_one])
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  have hτ : (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) =
      (H.W K 1 LL hA.2.2).emb i := AlgHom.ext fun x => hpt.1 x _ rfl
  let e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 := AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) hbij
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
    rw [← Nat.card_congr (e.arrowCongr AlgEquiv.refl), ← Nat.card_eq_of_bijective _ (H.W K 1 LL hA.2.2).emb_bij,
      Nat.card_zmod, e.toLinearEquiv.finrank_eq]
  obtain ⟨hdr, hspan⟩ := GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T.V T.ρ hc.1
  have hfil := GlobalTheory.Per.DdREqDcris.FildR_eq (P.PD K) T.ρ hbij.2
    (GlobalTheory.Per.DdREqDcris.map_Dcris_eq (P.PD K) T.ρ hbij.2 hspan) (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)
  rw [hτ] at hfil
  have hr := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI hT K LL T.V T.ρ).2 hcard hdr
    (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI hT K LL T.V T.ρ).1
  have : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) T.ρ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) T.ρ) inf_le_left
  obtain ⟨u, d, hu, hd, hs⟩ := GlobalTheory.Per.Sen.adapted_basis_jumps (DdRE (P.PD K) T.ρ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ))
    (FildR (P.PD K) T.ρ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)) (U i) _ hr
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.Per.FilCount.filV_antitone (P.PD K) hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.Per.FilCount.filV_exhaustive (P.PD K) (LL := ↥LL.1) x).imp fun a ha => ⟨hx, ha⟩)
    (fun x hx => GlobalTheory.Cmp.JumpDict.filV_sep (P.PD K) (LL := ↥LL.1) x fun a => (hx a).2)
    (hc.2 i _ fun x => congrArg (fun f => f x) hτ)
  refine ⟨u, d, hu, hd, GlobalTheory.SenLines.SplitFil.spanIsLines_of_graded _ u d _
    ((H.W K 1 LL hA.2.2).levN_supp T i ζ) hs ?_⟩
  refine ((h4 K 1 LL hA.2.2 T hc.1 i ζ).2.1 τ hpt).2.trans (congrArg _ (funext fun a => ?_))
  exact GlobalTheory.Per.FilLetUnram.toDR_FilLet _ T i _ a hbij.2 hτ (hfil a)

theorem completionLines_of_latticeAtLevels :
    (∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      ∀ (H : LocHW l P) (F : LocFon l P AI H) (C : LocCmpT l P AI H F),
        GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.LatticeAtLevels l P AI H F C) →
    GlobalTheory.SenLines.CompletionLines :=
  fun h4 l _ P AI hT H F C _ _ hA U T hc _ i ζ hζ =>
    linesAt_of_latticeAtLevels hT (h4 l P AI hT H F C) hA T U hc i ζ hζ

end GlobalTheory.SenLines.AllRoots
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvXPowMul
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.Approx

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_sum (e : PowerSeries L) (f : ℤ → M) (k : ℤ) (N : ℕ)
    (hN : ∀ j : ℕ, N ≤ j → f (k - j) = 0) :
    conv e f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j e • f (k - j) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hj (by rw [hN j (not_lt.1 hc), smul_zero])

theorem exists_bound {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (k : ℤ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → f (k - j) = 0 := by
  refine ⟨(k - m₀ + 1).toNat, fun j hj => hf _ ?_⟩
  have h1 := Int.self_le_toNat (k - m₀ + 1)
  have h2 : (((k - m₀ + 1).toNat : ℕ) : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  omega

theorem conv_add {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (e e' : PowerSeries L) :
    conv (e + e') f = conv e f + conv e' f := by
  funext k
  obtain ⟨N, hN⟩ := exists_bound hf k
  simp only [Pi.add_apply, conv_eq_sum _ f k N hN, map_add, add_smul, Finset.sum_add_distrib]

theorem conv_smul {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (c : L) (e : PowerSeries L) :
    conv (c • e) f = c • conv e f := by
  funext k
  obtain ⟨N, hN⟩ := exists_bound hf k
  simp only [Pi.smul_apply, conv_eq_sum _ f k N hN, map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem conv_smul_add {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (c : L) (e e' : PowerSeries L) :
    conv (c • (e + e')) f = c • conv e f + c • conv e' f := by
  rw [conv_smul hf, conv_add hf, smul_add]

theorem conv_X_pow_mul {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (m : ℕ) (p : PowerSeries L)
    (k : ℤ) : conv (PowerSeries.X ^ m * p) f k = conv p f (k - m) := by
  obtain ⟨N, hN⟩ := exists_bound hf (k - m)
  have hN' : ∀ j : ℕ, m + N ≤ j → f (k - j) = 0 := by
    intro j hj
    have := hN (j - m) (by omega)
    rwa [show k - (m : ℤ) - ((j - m : ℕ) : ℤ) = k - j by push_cast [show m ≤ j by omega]; ring] at this
  rw [conv_eq_sum _ f k _ hN', conv_eq_sum _ f (k - m) N hN, Finset.sum_range_add]
  rw [Finset.sum_eq_zero, zero_add]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), show m + j - m = j by omega]
    congr 2
    push_cast
    ring
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]

theorem combine {ι : Type} [Fintype ι] (F : ι → ℤ → M) (m₀ : ι → ℤ) (hbd : ∀ j, ∀ k < m₀ j, F j k = 0)
    (c : L) (e p : ι → PowerSeries L) (m : ℕ) (k : ℤ) :
    (∑ j, conv (c • (e j + PowerSeries.X ^ m * p j)) (F j)) k - c • (∑ j, conv (e j) (F j)) k =
      (∑ j, c • conv (p j) (F j)) (k - m) := by
  simp only [fun j => conv_smul_add (hbd j) c (e j) (PowerSeries.X ^ m * p j), Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, Finset.sum_add_distrib, Finset.smul_sum, fun j => conv_X_pow_mul (hbd j) m (p j) k]
  abel

end Series

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem approx : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ g ∈ Lat C h T i ζ, ∀ m : ℕ, ∃ (n : ↥(W.N T)) (c : ↥LL.1), c ≠ 0 ∧ ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ n j - c • g j = f (j - m) := by
  intro D HW F Cm l _ K s LL h W C T hT i ζ hζ g hg m
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := ⟨s, hζ⟩
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hFull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ
  obtain ⟨hsm, hB⟩ := GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ hζ' hFull
  obtain ⟨-, hspan, -⟩ := hB _ nb
  obtain ⟨e, rfl⟩ := hspan g hg
  have hW := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).2.2.1 i ζ hζ'
  choose a c hc hdiv using fun j => hW (e j) m
  choose p hp using hdiv
  haveI := LL.2
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ↥(OL LL)) c
  have ho : ∀ j, ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = (b : ↥(OL LL)) • c j :=
    fun j => RingHom.mem_rangeS.1 (hb j)
  choose o ho using ho
  obtain ⟨cc, hccd⟩ : ∃ x : ↥LL.1, x = algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) := ⟨_, rfl⟩
  have hcc : cc ≠ 0 := hccd ▸ IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have ho' : ∀ j, algebraMap ↥(OL LL) ↥LL.1 (o j) = cc * c j := by
    intro j
    rw [ho j, hccd, Algebra.smul_def]
  choose m0 hm0 using fun j => (C.C K s LL h).tie.levB_supp T i ζ (nb j)
  have hlev : ∀ j, W.lev i ζ (o j • a j) = cc • (e j + PowerSeries.X ^ m * p j) := by
    intro j
    rw [map_smul, ← algebraMap_smul ↥LL.1 (o j), ho' j, mul_smul, ← hp j, add_sub_cancel]
  have hbd : ∀ j, ∀ k < m0 j, ex C h T i ζ (nb j) k = 0 := hm0
  have hexn : ex C h T i ζ (∑ j, (o j • a j) • nb j) =
      ∑ j, conv (cc • (e j + PowerSeries.X ^ m * p j)) (ex C h T i ζ (nb j)) := by
    have := map_sum ((C.C K s LL h).tie.levB T i ζ) (fun j => (o j • a j) • nb j) Finset.univ
    refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← hlev j]
    exact hsm _ _
  refine ⟨∑ j, (o j • a j) • nb j, cc, hcc, ∑ j, cc • conv (p j) (ex C h T i ζ (nb j)),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p j, nb j, rfl⟩),
    fun k => ?_⟩
  rw [hexn]
  exact combine _ m0 hbd cc e p m k

end GlobalTheory.NL.Approx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisStrictHodgeFiltrationUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.CrisStrict

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem ιV_map (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V') (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) =
      AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [ιV]

theorem map_mem_Dcris (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x ∈ Dcris PD ρ' := by
  have key : ∀ (g : G) (z : V ⊗[Qp] B), actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) =
      AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v b => simp [actVB, hf]
  rw [GlobalTheory.Per.CrisDR.mem_Dcris_iff] at hx ⊢
  intro g
  rw [key, hx g]

theorem map_mem_FilV (f : V →ₗ[LL] V') {a : ℤ} {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f (LinearMap.id) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp

theorem map_map_id {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
    (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map g (LinearMap.id : BdR →ₗ[Qp] BdR)
      (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) =
      AlgebraTensorModule.map (g ∘ₗ f) (LinearMap.id : BdR →ₗ[Qp] BdR) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp

theorem mem_FilV_of_injective (f : V →ₗ[LL] V') (hi : Function.Injective f) {a : ℤ} {x : V ⊗[Qp] BdR}
    (hx : AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a) :
    x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.2 hi)
  have := map_mem_FilV PD g hx
  rwa [map_map_id, hg, AlgebraTensorModule.map_id, LinearMap.id_apply] at this

end Abstract

theorem dcris_strict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → (Function.Surjective π → IsCrys (P.PD K) ρ₁ → ∀ a : ℤ, (FilCris (P.PD K) ρ₁ a).map (AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) = FilCris (P.PD K) ρ₂ a) ∧ (Function.Injective π → ∀ a : ℤ, ∀ y ∈ Dcris (P.PD K) ρ₁, AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) y ∈ FilCris (P.PD K) ρ₂ a → y ∈ FilCris (P.PD K) ρ₁ a) := by
  intro l _ P AI T K LL hb V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ π hπ
  refine ⟨fun hs hc a => le_antisymm ?_ ?_, fun hi a y hy hF => ?_⟩
  · rintro _ ⟨x, ⟨hxD, hxF⟩, rfl⟩
    refine ⟨map_mem_Dcris (P.PD K) ρ₁ ρ₂ π hπ hxD, Submodule.mem_comap.2 ?_⟩
    rw [ιV_map]
    exact map_mem_FilV (P.PD K) π (Submodule.mem_comap.1 hxF)
  · rintro y ⟨hyD, hyF⟩
    have hc2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hc).1
    have hyR : ιV (P.PD K) (LL := ↥LL.1) (V := V₂) y ∈ DdR (P.PD K) ρ₂ := by
      rw [← (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI T K LL hb V₂ ρ₂ hc2).1]
      exact Submodule.mem_map_of_mem hyD
    have hdr1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL V₁ ρ₁ hc).1
    obtain ⟨x', ⟨hx'D, hx'F⟩, hx'⟩ :=
      ((GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hdr1).2 a _ ⟨hyR, hyF⟩
    rw [← (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI T K LL hb V₁ ρ₁ hc).1] at hx'D
    obtain ⟨x, hx, rfl⟩ := hx'D
    refine ⟨x, ⟨hx, hx'F⟩, ?_⟩
    apply GlobalTheory.Per.DdREqDcris.ιV_injective (P.PD K) (LL := ↥LL.1)
    rw [ιV_map, hx']
  · refine ⟨hy, ?_⟩
    have h2 := Submodule.mem_comap.1 hF.2
    rw [ιV_map] at h2
    exact Submodule.mem_comap.2 (mem_FilV_of_injective (P.PD K) π hi h2)

end GlobalTheory.Per.CrisStrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinApproxRootGaloisSubMemBdRFilStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n M : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X →
    bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) →
    ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev q) - bk.ev q) ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.BSP.approxRoot_gal_sub_mem_fil) | (exact GlobalTheory.BSP.approxRoot_gal_sub_mem_fil) | (intros; apply GlobalTheory.BSP.approxRoot_gal_sub_mem_fil  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, bk.ρ₀ ≤ ρ → ρ < 1 → (∀ y : Disc l (s X) ρ, ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖) ∧ ∀ R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀, IsDiscMap (RingHom.id A) R → ∀ (h : ℕ) (y : Disc l (s X) ρ), toDisc l (s X) bk.ρ₀ (s bk.E) ^ h ∣ R y → toDisc l (s X) ρ (s bk.E) ^ h ∣ y := by
  first | exact @GlobalTheory.BSP.div_E_of_topBasis | exact GlobalTheory.BSP.div_E_of_topBasis | (intros; apply GlobalTheory.BSP.div_E_of_topBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvaluationPowerSeriesShiftStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_power_series_shift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : PowerSeries ↥K.1), OnDisc l (oK K) L →
    ∀ (x : AK K), thetaK K x = 0 → ∀ y : GlobalTheory.AcrisK.BK K, Ev L x y →
    ∃ (L' : PowerSeries ↥K.1) (u : GlobalTheory.AcrisK.BK K), OnDisc l (oK K) L' ∧
      (∀ k, PowerSeries.coeff k L' = PowerSeries.coeff (k + 1) L) ∧ Ev L' x u ∧
      y = inK K (PowerSeries.coeff 0 L) + toB K (ofA K x) * u := by
  first | exact @GlobalTheory.AcrisK.ev_shift | exact GlobalTheory.AcrisK.ev_shift | (intros; apply GlobalTheory.AcrisK.ev_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAbelianizedGaloisHomOfClosureIsoStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianizedGalois_hom_of_closureIso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (φ : Ω ≃+* Ω') (j : E →+* E'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) → ∃ ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω, Continuous ρ ∧ ∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  first | exact @GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv | exact GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv | (intros; apply GlobalTheory.HeckeGal.exists_abHom_of_ringEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaLimitBdRPlusDeRhamFrame
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem exists_beta_limit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ), F.IsDR → ∃ B : Matrix (Fin d) (Fin d) (Per.BdRp l), ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m := by
  intro l _ K bk N d ρ F hF
  choose k β hβ using hF
  have mono : ∀ {m n : ℕ}, m ≤ n → ∀ {k' : ℕ} {β' : Matrix (Fin d) (Fin d) bk.S}, F.IsBeta n k' β' → F.IsBeta m k' β' :=
    fun h _ _ hb => ⟨hb.1, fun g i j => (pow_dvd_pow _ h).trans (hb.2 g i j)⟩
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  obtain ⟨hfil, -, hcomp, -⟩ := GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE
  obtain ⟨v, hv⟩ := (isUnit_l_BdRp l).exists_left_inv
  have hvk : ∀ a : ℕ, v ^ a * (l : Per.BdRp l) ^ a = 1 := fun a => by rw [← mul_pow, hv, one_pow]
  set X : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => aDp l (bk.ev (β n i j)) with hX
  set x : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => v ^ k n * X n i j with hx
  have cauchy : ∀ m n, m ≤ n → ∀ i j, x n i j - x m i j ∈ Per.FilP l m := by
    intro m n hmn i j
    have h := GlobalTheory.T.breuilKisin_beta_unique_mod_E_pow l K bk m N d ρ F (k m) (k n) (β m) (β n) (hβ m) (mono hmn (hβ n)) i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    have h2 : bk.ev bk.E ^ m ∣ bk.ev ((l : bk.S) ^ k n * β m i j - (l : bk.S) ^ k m * β n i j) := by
      rw [← map_pow]; exact map_dvd bk.ev h
    have h3 := ((GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk m).2.2.1 _).2 h2
    simp only [map_sub, map_mul, map_pow, map_natCast] at h3
    have h4 := Ideal.mul_mem_left (Per.FilP l m) (-(v ^ k n * v ^ k m)) h3
    convert h4 using 1
    simp only [hx, hX]
    linear_combination (v ^ k m * aDp l (bk.ev (β m i j))) * hvk (k n) - (v ^ k n * aDp l (bk.ev (β n i j))) * hvk (k m)
  have hmem : ∀ (n : ℕ) (y : Per.BdRp l), y ∈ (Ideal.span {aDp l (xi e)} ^ n • ⊤ : Submodule (Per.BdRp l) (Per.BdRp l)) ↔
      y ∈ Per.FilP l n := by
    intro n y
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hfil]
  have lim : ∀ i j, ∃ L : Per.BdRp l, ∀ n, x n i j - L ∈ Per.FilP l n := by
    intro i j
    obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := fun n => x n i j) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hmem, ← neg_sub]
      exact (Per.FilP l m).neg_mem (cauchy m n hmn i j))
    exact ⟨L, fun n => (hmem n _).1 (SModEq.sub_mem.1 (hL n))⟩
  choose B hB using lim
  refine ⟨Matrix.of B, fun m => ⟨k m, β m, hβ m, fun i j => ?_⟩⟩
  have h := Ideal.mul_mem_left (Per.FilP l m) ((l : Per.BdRp l) ^ k m) (hB i j m)
  convert h using 1
  simp only [Matrix.of_apply, hx, hX]
  linear_combination (-(aDp l (bk.ev (β m i j)))) * hvk (k m)

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatiblePowerSeriesValueStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_power_series_value : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ω : ℕ → AK K) (G : PowerSeries ↥(OL K)) (u : ℕ → OC l),
    (∀ n, frobq K (ω (n + 1)) = ω n) → (∀ n, ‖((thetaK K (ω n) : OC l) : ℂ_[l])‖ < 1) →
    (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i G) * thetaK K (ω n) ^ i : OC l) : ℂ_[l])) (u n : ℂ_[l])) →
    ∃ y : ℕ → AK K, (∀ n, frobq K (y (n + 1)) = y n) ∧ (∀ n, thetaK K (y n) = u n) ∧
      ∀ M : ℕ, ω 0 ^ M ∣ y 0 - ∑ j ∈ Finset.range M, inO K (PowerSeries.coeff j G) * ω 0 ^ j := by
  first | exact @GlobalTheory.FrobChainSeries.main | exact GlobalTheory.FrobChainSeries.main | (intros; apply GlobalTheory.FrobChainSeries.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusLiftLubinTateStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_lift_lubin_tate : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ x : OCb l,
    ∃ ω : AK K, red K ω = x ∧ frobq K ω = inO K π * ω + ω ^ l ^ fK K := by
  first | exact @GlobalTheory.ColmezLift.exists_lift | exact GlobalTheory.ColmezLift.exists_lift | (intros; apply GlobalTheory.ColmezLift.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgIdentityProdOfUnitResultantStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involutiveAlg_identity_prod_of_unit_resultant : ∀ (K : UQ) (B₁ B₂ C₁ C₂ : InvAlg K), ((B₁.P * B₂.P) * (C₁.P * C₂.P)).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → IsIntegral K.O C₁.g → IsIntegral K.O C₂.g → val K.O (resultant (B₁.P * B₂.P) (C₁.P * C₂.P)) = 0 → InvAlg.Identity B₁ B₂ → InvAlg.Identity C₁ C₂ → InvAlg.Identity (B₁.prod C₁) (B₂.prod C₂) := by
  first | exact @GlobalTheory.UnitLemma.ProdId.identity_prod | exact GlobalTheory.UnitLemma.ProdId.identity_prod | (intros; apply GlobalTheory.UnitLemma.ProdId.identity_prod <;> assumption)
end

