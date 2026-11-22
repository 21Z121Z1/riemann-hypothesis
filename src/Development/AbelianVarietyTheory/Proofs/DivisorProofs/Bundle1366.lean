import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEqSmulOfIsot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThreeRankOneSphericalVectorCellValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTerms
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

open GlobalTheory.BCT

theorem mem_map_conj_iff_term {G : Type} [Group G] (K : Subgroup G) (y z : G) :
    z ∈ K.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem cptPart_le_self_term {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T :=
  Subgroup.closure_le _ |>.mpr fun _ ht => ht.1

theorem inf_relIndex_of_le_left_term {G : Type} [Group G] {A B C : Subgroup G} (h : C ≤ A) :
    (A ⊓ B).relIndex C = B.relIndex C := by
  unfold Subgroup.relIndex
  congr 1
  ext ⟨c, hc⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact and_iff_right (h hc)

theorem avg_eq_one_of_forall_term {H : Type} [Group H] (u : H → ℂ) (hu : ∀ k, u k = 1) : avg u = 1 := by
  have hs : rStab u = ⊤ := by
    ext k; simp only [Subgroup.mem_top, iff_true]; intro x; rw [hu, hu]
  have hi : (rStab u).index = 1 := Subgroup.index_eq_one.2 hs
  have hsub : Subsingleton (H ⧸ rStab u) := by
    have hc : Nat.card (H ⧸ rStab u) = 1 := hi
    exact (Nat.card_eq_one_iff_unique.1 hc).1
  unfold avg
  rw [hi, finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ rStab u) (fun q hq => absurd (Subsingleton.elim q _) hq), hu]
  simp

theorem twTerm_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v) → ∀ x, GlobalTheory.EulerAbs.twTerm θ (⨅ v, (K v).comap (pf v)) δ f x = ∏ᶠ v, GlobalTheory.EulerAbs.twTerm (θv v) (K v) (pf v δ) (fv v) (pf v x) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hK δ f fv hf hcomm hstab hwt hev x
  have hT : ∀ y, y ∈ twCent θ δ ↔ ∀ v, pf v y ∈ twCent (θv v) (pf v δ) := fun y => GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff pf K hX θ θv hθ δ y
  have hC : ∀ y, y ∈ cptPart (twCent θ δ) ↔ ∀ v, pf v y ∈ cptPart (twCent (θv v) (pf v δ)) :=
    GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) hT hcomm
  have hgood := hev.and (hX.eventually_mem x)
  have hCg : cptPart (twCent θ δ) = ⨅ v, (cptPart (twCent (θv v) (pf v δ))).comap (pf v) := by
    ext y; rw [hC, Subgroup.mem_iInf]; rfl
  have hHg : (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom =
      ⨅ v, ((K v).map (MulAut.conj (pf v x)).toMonoidHom).comap (pf v) := by
    ext y
    simp only [mem_map_conj_iff_term, Subgroup.mem_iInf, Subgroup.mem_comap, map_mul, map_inv]
  have hloc : ∀ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) = ((K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := fun v => inf_relIndex_of_le_left_term (cptPart_le_self_term _)
  have hCH : ∀ᶠ v in cofinite, cptPart (twCent (θv v) (pf v δ)) ≤ (K v).map (MulAut.conj (pf v x)).toMonoidHom :=
    hgood.mono fun v hv c hc => by
      rw [mem_map_conj_iff_term]
      exact mul_mem (mul_mem (inv_mem hv.2) (hv.1.2.2 hc)) hv.2
  have hrel : (twCent θ δ ⊓ (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom).relIndex
      (cptPart (twCent θ δ)) = ∏ᶠ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := by
    rw [inf_relIndex_of_le_left_term (cptPart_le_self_term _), hHg, hCg]
    simp only [hloc]
    exact GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod pf K hX (fun v => cptPart (twCent (θv v) (pf v δ)))
      (fun v => (K v).map (MulAut.conj (pf v x)).toMonoidHom)
      (fun v => by rw [← hloc]; exact (hwt v (pf v x)).2) hCH
  let u : ∀ v, K v → ℂ := fun v k => fv v ((pf v x * k)⁻¹ * pf v δ * θv v (pf v x * k))
  have hfun : (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩ := by
    funext k; rw [hf]; congr 1; funext v; simp only [u, map_mul, map_inv, hθ]
  have hu1 : ∀ᶠ v in cofinite, ∀ k, u v k = 1 := hgood.mono fun v hv k => by
    have hk : pf v x * (k : Y v) ∈ K v := mul_mem hv.2 k.2
    simp only [u]
    rw [hv.1.1, Set.indicator_of_mem (show _ ∈ (K v : Set (Y v)) from
      mul_mem (mul_mem (inv_mem hk) hv.1.2.1) (hK v _ hk))]
    rfl
  have havg : avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      ∏ᶠ v, avg (u v) := by
    rw [hfun]; exact GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod pf K hX u (fun v => hstab v (pf v x)) hu1
  have hfa : Function.HasFiniteMulSupport fun v => (((twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) : ℕ) : ℂ) :=
    (eventually_cofinite.1 hCH).subset fun v hv h => hv (by
      show ((_ : ℕ) : ℂ) = 1
      rw [hloc, Subgroup.relIndex_eq_one.2 h, Nat.cast_one])
  have hfb : Function.HasFiniteMulSupport fun v => avg (u v) :=
    (eventually_cofinite.1 hu1).subset fun v hv h => hv (avg_eq_one_of_forall_term _ h)
  unfold twTerm
  rw [hrel, havg, Nat.cast_finprod', ← finprod_mul_distrib hfa hfb]

end GlobalTheory.EulerAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartLeEigensystemPartPrincipalLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.PartTypeW

theorem part_in_eigenpart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, principalLevelFrame.IsEigOf (PW i0) (levS _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) (levChi _ (R.βW i0) (R.datWp i0 (R.levL F false (sg0 D A)))) SF π c → ∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π, ∃ x ∈ Wcc R SF i c, (R.HW i _).e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _hOk hC SF hSF n hF PY PW _hPY hPW π i0 c hEig i U hU
  have hLev := hC.lev

  have hN : ∀ (cc : ℕ) (P : Pl D.host.E), (((1 ^ cc : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro cc P h
    rw [one_pow, Nat.cast_one] at h
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have LO := fun (j : Fin D.R.m) (Lv : LevelP R.Pg D.R.r ℂ) (P : Pl D.host.E) (hG : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D j) (R.βW j) (R.ΛW j) _ (R.datWp j Lv) (hLev.βW j).choose_spec P
      (hN _ P) (fun PP h => hG PP (h.imp id (fun h' => absurd h' (Finset.notMem_empty _))))
  have hGood := fun P => (GlobalTheory.GoodPrimes.good_primes R F hLev).2.2.1 SF hSF P

  have hU' := hU
  simp only [principalLevelFrame.isotL, Mult.goodPart, Submodule.mem_inf, LinearMap.mem_ker] at hU'
  obtain ⟨⟨hUM, hUe⟩, hUiso⟩ := hU'

  have hle : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      k ∈ levS (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) ∧
        levChi (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) k =
          levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k := by
    intro k hk
    obtain ⟨h1, h2⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) (R.levL F false (sg0 D A)) k hk
    obtain ⟨_, h3⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) R.triv k hk
    exact ⟨h1, h2.trans h3.symm⟩
  have hU0 : U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) :=
    GlobalTheory.HeckeParts.mult_mono hle hUM

  have hrange := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, hx⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrange]; exact hU0
  refine ⟨x, ?_, hx⟩
  rw [GlobalTheory.Hk3.Wcc, Submodule.mem_comap, hx]
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hU0, LinearMap.mem_ker.2 hUe⟩, Submodule.mem_inf.2 ⟨hU0, ?_⟩⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  obtain ⟨_, _, _, _, hoff, -⟩ := id hB
  have hG : Good R A.μ0 P := (hGood P).1 hoff
  have hSph : SphOp (Wc D i) P d B := (((LO i R.triv P hG).2.1 SF d B).1 hB).2
  obtain ⟨B0, hB0⟩ : IsLab (Wc D i0) P d :=
    (GlobalTheory.LabEq.isLab_W_iff (s := s) R F hC i0 P d hG).2.2
      ((GlobalTheory.LabEq.isLab_W_iff (s := s) R F hC i P d hG).2.1 ⟨B, hSph⟩)
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalHecke_scalar_on_spherical_vectors hF (PW i0) (hPW i0) π P d B0 hB0
  obtain ⟨⟨x0, hx0S, hx0, hx0T⟩, hEigOp, -⟩ := hEig
  have hB0full := ((LO i0 (R.levL F false (sg0 D A)) P hG).2.1 SF d B0).2 ⟨hoff, hB0⟩
  have hfix0 : ∀ κ, (PW i0).ψ κ ∈ hyp (Wc D i0) P → Formalism.L2.NG.rt D.host.E n κ x0 = x0 := by
    intro κ hκ
    obtain ⟨h1, h2⟩ := (LO i0 (R.levL F false (sg0 D A)) P hG).1 _ hκ
    rw [hx0T κ h1]
    simp only [h2, one_smul]
  have hac : a = c P d := by
    have e2 := hEigOp P d B0 hB0full x0 hx0S hx0T
    rw [ha x0 hx0S hfix0] at e2
    exact smul_left_injective ℂ hx0 e2
  obtain ⟨hiff, htr⟩ := GlobalTheory.T.sphericalEigenvalues_independent_of_standardFrame hF (PW i) (PW i0) (hPW i) (hPW i0) P d
  have hvec : ∀ y ∈ π.S, (∀ κ, (PW i).ψ κ ∈ hyp (Wc D i) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
      principalLevelFrame.Hecke₃ (PW i) B y = c P d • y := by
    intro y hy hfy
    rw [htr B B0 hSph hB0 y hfy, ha y hy (fun κ hκ => hfy κ ((hiff κ).2 hκ)), hac]
  have hUfix : ∀ k ∈ hyp (Wc D i) P, postOn (R.MW i (sg0 D A)) (principalLevelFrame.rtA k) U = U := by
    intro k hk
    obtain ⟨h1, h2⟩ := (LO i (R.levL F false (sg0 D A)) P hG).1 k hk
    have hl := principalLevelFrame.mult_lev hUM
    apply MultilinearMap.ext
    intro v
    funext g
    rw [Mult.postOn_apply]
    show U v (g * k) = U v g
    rw [hl v k h1 g, h2, one_mul]
  exact GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF (PW i) (hPW i) R.θ (R.MW i (sg0 D A)) π P d B (c P d) hSph hvec U hUiso hUfix

end GlobalTheory.PartTypeW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThreeRankOneSphericalVectorCellValueStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryThreeRankOne_sphericalVector_cell_value : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ u : cellU y, φ (y⁻¹ * (u : GU σ n)) = (α k / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) := by
  first | exact @GlobalTheory.WeylCell.U21HeisenbergElement.value_point | exact GlobalTheory.WeylCell.U21HeisenbergElement.value_point | (intros; apply GlobalTheory.WeylCell.U21HeisenbergElement.value_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroupStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryWeylCellShell_isOpenCompactSubgroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    (∀ j : ℤ, IsOpen (shellU k y j) ∧ IsCompact (shellU k y j) ∧ (1 : cellU y) ∈ shellU k y j ∧
      (∀ u v : cellU y, u ∈ shellU k y j → v ∈ shellU k y j → u * v ∈ shellU k y j) ∧
      (∀ u : cellU y, u ∈ shellU k y j → u⁻¹ ∈ shellU k y j)) ∧
    shellU k y 0 = (((KU σ n).subgroupOf (cellU y) : Subgroup (cellU y)) : Set (cellU y)) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup | exact GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishTransferOfVanishOverAlgebraicClosure
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem vanish_transfer_of_algClosure :
    ∀ (F σ : Type) [Field F] [Finite σ] (J : Ideal (MvPolynomial σ F)) (f : MvPolynomial σ F),
      (∀ x : σ → AlgebraicClosure F, (∀ g ∈ J, aeval x g = 0) → aeval x f = 0) →
      ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (x : σ → Ω), (∀ g ∈ J, aeval x g = 0) →
        aeval x f = 0 := by
  intro F σ _ _ J f hf Ω _ _ x hx
  have hrad : f ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure F)]
    exact fun y hy => hf y hy
  obtain ⟨m, hm⟩ := hrad
  have h0 : (aeval x f) ^ m = 0 := by
    rw [← map_pow]
    exact hx _ hm
  exact IsNilpotent.eq_zero ⟨m, h0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleTwistOfGeneratedAndVeryAmpleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryAmple_twist_of_generated_and_veryAmple : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H M : LB X) (n m : ℕ) (s : Fin (n + 1) → LB.Sec H) (u : Fin (m + 1) → LB.Sec M), H.IsLB → M.IsLB → VeryAmpleBy f H s → (⨆ a, nonzeroLocus (u a) = ⊤) → ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.tw M H 1)), VeryAmpleBy f (GlobalTheory.AbLaw.tw M H 1) s' := by
  first | exact @GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | exact GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated | (intros; apply GlobalTheory.GenTwist.veryAmpleBy_tw_of_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIdxRatio
section
noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount.OrbKProd

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd

theorem finsum_prod_mul {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact finsum_prod_mul_of_finite u v hu hv
    · rw [finsum_of_infinite_support hv, mul_zero]
      by_cases h0 : ∀ a, u a = 0
      · simp [h0]
      · push_neg at h0
        obtain ⟨a, ha⟩ := h0
        apply finsum_of_infinite_support
        intro hfin
        apply hv
        refine (hfin.image Prod.snd).subset ?_
        intro b hb
        exact ⟨(a, b), by simp only [Function.mem_support] at hb ⊢; exact mul_ne_zero ha hb, rfl⟩
  · rw [finsum_of_infinite_support hu, zero_mul]
    by_cases h0 : ∀ b, v b = 0
    · simp [h0]
    · push_neg at h0
      obtain ⟨b, hb⟩ := h0
      apply finsum_of_infinite_support
      intro hfin
      apply hu
      refine (hfin.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, b), by simp only [Function.mem_support] at ha ⊢; exact mul_ne_zero ha hb, rfl⟩

section Vol

variable {G : Type} [Group G]

theorem vol_eq_idxRatio (C H : Subgroup G) : vol C H = GlobalTheory.FunObj.idxRatio H C := rfl

theorem vol_prod {G' : Type} [Group G'] (C H : Subgroup G) (C' H' : Subgroup G') :
    vol (C.prod C') (H.prod H') = vol C H * vol C' H' := by
  unfold vol
  rw [relIndex_prod_prod, relIndex_prod_prod]
  push_cast
  exact mul_div_mul_comm _ _ _ _

theorem map_conj_mul (K : Subgroup G) (t x : G) :
    K.map (MulAut.conj (t * x)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
  have h := map_conj_mul_three_subgroup_of_mem K K.one_mem t x
  rwa [mul_one] at h

theorem inf_map_conj (T A : Subgroup G) {t : G} (ht : t ∈ T) :
    T ⊓ A.map (MulAut.conj t).toMonoidHom = (T ⊓ A).map (MulAut.conj t).toMonoidHom := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective, map_conj_self _ ht]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem conj_isOpen {K : Subgroup G} (hKo : IsOpen (K : Set G)) (g : G) :
    IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have e : ((MulAut.conj g).toMonoidHom : G → G) = (fun y => y * g⁻¹) ∘ (fun y => g * y) := by
    funext y; simp [MulAut.conj_apply]
  rw [e]
  exact ((isOpenMap_mul_right g⁻¹).comp (isOpenMap_mul_left g)) _ hKo

theorem conj_isCompact {K : Subgroup G} (hKc : IsCompact (K : Set G)) (g : G) :
    IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  exact hKc.image (by show Continuous fun y : G => g * y * g⁻¹; fun_prop)

theorem vol_conj (T K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    {t : G} (ht : t ∈ T) (hvol : vol (T ⊓ K) ((T ⊓ K).map (MulAut.conj t).toMonoidHom) = 1) (x : G) :
    vol (T ⊓ K) ((T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom) =
      vol (T ⊓ K) (T ⊓ K.map (MulAut.conj x).toMonoidHom) := by
  have hc := GlobalTheory.FunObj.idxRatio_cocycle T (conj_isOpen hKo (t * x)) (conj_isCompact hKc (t * x))
    (conj_isOpen hKo t) (conj_isCompact hKc t) hKo hKc
  rw [map_conj_mul, inf_map_conj T _ ht, inf_map_conj T _ ht, GlobalTheory.FunObj.idxRatio_map (MulAut.conj t).injective,
    show GlobalTheory.FunObj.idxRatio ((T ⊓ K).map (MulAut.conj t).toMonoidHom) (T ⊓ K) = 1 from hvol, mul_one] at hc
  rw [vol_eq_idxRatio, vol_eq_idxRatio]
  exact hc.symm

end Vol

section Term

variable {G : Type} [Group G]

def oTerm (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) (x : G) : ℂ :=
  ((vol C (twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom) : ℚ) : ℂ)⁻¹ * f (x⁻¹ * δ * θ x)

theorem orbC_eq (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) :
    orbC θ K C δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), oTerm θ K C δ f (Quotient.out q) :=
  rfl

theorem f_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    f ((t * x * k)⁻¹ * δ * θ (t * x * k)) = f (x⁻¹ * δ * θ x) := by
  have ht0 : t * δ = δ * θ t := ht
  have ht' : θ t = δ⁻¹ * (t * δ) := eq_inv_mul_of_mul_eq ht0.symm
  rw [← hf k hk (x⁻¹ * δ * θ x)]
  congr 1
  simp only [map_mul, _root_.mul_inv_rev, ht']
  group

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem oTerm_inv (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (hf : ∀ k ∈ K, ∀ y, f (k⁻¹ * y * θ k) = f y)
    (hvol : ∀ t ∈ twCent θ δ, vol (twCent θ δ ⊓ K) ((twCent θ δ ⊓ K).map (MulAut.conj t).toMonoidHom) = 1)
    {t k : G} (ht : t ∈ twCent θ δ) (hk : k ∈ K) (x : G) :
    oTerm θ K (twCent θ δ ⊓ K) δ f (t * x * k) = oTerm θ K (twCent θ δ ⊓ K) δ f x := by
  unfold oTerm
  rw [f_inv θ K δ f hf ht hk x, map_conj_mul_three_subgroup_of_mem K hk, inf_map_conj _ _ ht,
    vol_conj _ K hKo hKc ht (hvol t ht) x]

theorem oTerm_prod {G' : Type} [Group G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G')
    (δ : G) (δ' : G') (f : G → ℂ) (f' : G' → ℂ) (x : G) (x' : G') :
    oTerm (θ.prodMap θ') (K.prod K') ((twCent θ δ).prod (twCent θ' δ') ⊓ K.prod K') (δ, δ')
        (fun y => f y.1 * f' y.2) (x, x') =
      oTerm θ K (twCent θ δ ⊓ K) δ f x * oTerm θ' K' (twCent θ' δ' ⊓ K') δ' f' x' := by
  unfold oTerm
  rw [twCent_prod, map_conj_prod, prod_inf_prod, prod_inf_prod, vol_prod]
  push_cast
  rw [mul_inv, mul_mul_mul_comm]
  rfl

end Term

theorem orbK_prod : ∀ {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [T2Space G₁] [T2Space G₂] (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ₁ : G₁) (δ₂ : G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ), Continuous θ₁ → Continuous θ₂ → IsCompact (K₁ : Set G₁) → IsOpen (K₁ : Set G₁) → IsCompact (K₂ : Set G₂) → IsOpen (K₂ : Set G₂) → (∀ k ∈ K₁, ∀ y, f₁ (k⁻¹ * y * θ₁ k) = f₁ y) → (∀ k ∈ K₂, ∀ y, f₂ (k⁻¹ * y * θ₂ k) = f₂ y) → (∀ t ∈ GlobalTheory.BCT.twCent θ₁ δ₁, vol (GlobalTheory.BCT.twCent θ₁ δ₁ ⊓ K₁) ((GlobalTheory.BCT.twCent θ₁ δ₁ ⊓ K₁).map (MulAut.conj t).toMonoidHom) = 1) → (∀ t ∈ GlobalTheory.BCT.twCent θ₂ δ₂, vol (GlobalTheory.BCT.twCent θ₂ δ₂ ⊓ K₂) ((GlobalTheory.BCT.twCent θ₂ δ₂ ⊓ K₂).map (MulAut.conj t).toMonoidHom) = 1) → orbK (θ₁.prodMap θ₂) (K₁.prod K₂) (δ₁, δ₂) (fun x => f₁ x.1 * f₂ x.2) = orbK θ₁ K₁ δ₁ f₁ * orbK θ₂ K₂ δ₂ f₂ := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ θ₁ θ₂ K₁ K₂ δ₁ δ₂ f₁ f₂ _ _ hK₁c hK₁o hK₂c hK₂o hf₁ hf₂ hv₁ hv₂
  unfold orbK
  rw [orbC_eq, orbC_eq, orbC_eq, twCent_prod]
  have hz : ∀ z, oTerm (θ₁.prodMap θ₂) (K₁.prod K₂) ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂) ⊓ K₁.prod K₂) (δ₁, δ₂)
      (fun y => f₁ y.1 * f₂ y.2)
      (Quotient.out (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂) z)) =
      oTerm θ₁ K₁ (twCent θ₁ δ₁ ⊓ K₁) δ₁ f₁ (Quotient.out z.1) *
        oTerm θ₂ K₂ (twCent θ₂ δ₂ ⊓ K₂) δ₂ f₂ (Quotient.out z.2) := by
    intro z
    obtain ⟨a, b, ha, hb, e⟩ := DoubleCoset.mk_out_eq_mul ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂)) (K₁.prod K₂)
      (Quotient.out z.1, Quotient.out z.2)
    rw [Subgroup.mem_prod] at ha hb
    have e2 : Quotient.out (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂) z) =
        (a.1 * Quotient.out z.1 * b.1, a.2 * Quotient.out z.2 * b.2) := e
    rw [e2, oTerm_prod, oTerm_inv θ₁ K₁ δ₁ f₁ hK₁c hK₁o hf₁ hv₁ ha.1 hb.1,
      oTerm_inv θ₂ K₂ δ₂ f₂ hK₂c hK₂o hf₂ hv₂ ha.2 hb.2]
  have hq := finsum_comp_equiv (Equiv.ofBijective _ (dcPair_bij (twCent θ₁ δ₁) K₁ (twCent θ₂ δ₂) K₂))
    (f := fun q => oTerm (θ₁.prodMap θ₂) (K₁.prod K₂) ((twCent θ₁ δ₁).prod (twCent θ₂ δ₂) ⊓ K₁.prod K₂) (δ₁, δ₂)
      (fun y => f₁ y.1 * f₂ y.2) (Quotient.out q))
  rw [← hq, finsum_congr hz]
  exact finsum_prod_mul (fun q => oTerm θ₁ K₁ (twCent θ₁ δ₁ ⊓ K₁) δ₁ f₁ (Quotient.out q))
    (fun q => oTerm θ₂ K₂ (twCent θ₂ δ₂ ⊓ K₂) δ₂ f₂ (Quotient.out q))

end GlobalTheory.LKCount.OrbKProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WFormsPartsOfDistinctTypesOrthogonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.W_forms_parts_of_distinct_types_orthogonal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ i p q, p ≠ q → ∀ w ∈ R.Wp3 i p, ∀ w' ∈ R.Wp3 i q, ⟪w, w'⟫_ℂ = 0 := by
  first | exact @GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne | exact GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne | (intros; apply GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameEigenvectorColumnForm
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.TorusCentRow

theorem row_scalar : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {g : GAd σ J} {k : Fin r} (γ : AF F ⊗[F] E),
    (matHom _ σ J g⁻¹).1 *ᵥ (fun i => adMat F Y i k) = γ • (fun i => adMat F Y i k) → ∀ i,
    (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1) k i =
      (adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 * adMat F X) k k * adMat F (cT (σ : E →+* E) Y * J) k i := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW g k γ hγ i
  set S := sigR (AF F) σ with hS
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef
  set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef
  have hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹ := map_inv _ g
  have hMMi : M * Mi = 1 := by
    rw [hMdef, hMidef, hinv]; exact Units.mul_inv _
  have hU : cT S M * adMat F J * M = adMat F J := g.2
  have hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J := by
    rw [adMat, Matrix.map_mul]
    congr 1
  have hJM : adMat F J * M = cT S Mi * adMat F J := by
    calc adMat F J * M = (cT S Mi * cT S M) * adMat F J * M := by
          rw [← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
      _ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]
      _ = cT S Mi * adMat F J := by rw [hU]
  have hcol : ∀ j, (Mi * adMat F Y) j k = γ * adMat F Y j k := by
    intro j
    have := congrFun hγ j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hrow : ∀ i, (adMat F (cT (σ : E →+* E) Y * J) * M) k i
      = S γ * adMat F (cT (σ : E →+* E) Y * J) k i := by
    intro i
    rw [hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul]
    simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, hcol, map_mul,
      Finset.mul_sum, mul_assoc]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hkk : (adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X) k k = S γ := by
    rw [Matrix.mul_apply]
    simp_rw [hrow, mul_assoc, ← Finset.mul_sum, ← Matrix.mul_apply, hyx, Matrix.one_apply_eq, mul_one]
  rw [hkk, hrow]

end GlobalTheory.TorusCentRow
end

