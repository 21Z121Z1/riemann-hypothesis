import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0001
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0901
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0897
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionOfEigenCentralSeries
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.PassOp

open Formalism.MainNotions.N.PlaceLabelTeichmuller

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem prod_plc (a : ∀ i, MonoidAlgebra ℂ (G i)) (L : List ι) (hL : L.Nodup) :
    (L.map fun i => plc i (a i)).prod = tens (fun j => if j ∈ L then a j else 1) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]
    exact tens_one.symm
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ih hL.2, plc, tens_mul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [hL.1]
    · simp [Function.update_of_ne hj, hj]

end Tensor

local instance factGk (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroGk (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem tw_eta (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).1)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem twistIso_eta (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    (L : List (Part D.naut.CG)) (hL : ∀ p ∈ L, 1 ≤ p.a) :
    twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv = L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    show (⟨p.a, D.naut.tw (D.naut.tw p.π D.naut.etaT) D.naut.etaTinv, p.d⟩ : Part D.naut.CG) ::
      twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv = p :: L
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)), tw_eta D hT hAN (hL p List.mem_cons_self)]

theorem goodPar_iff_goodSig (D : D7) (Sig : List (Part D.naut.CG)) (σ' : D.ntypes.Par)
    (h1 : ∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) :
    D.ntypes.goodPar σ' ↔ goodSig D.nd D.naut Sig := by
  unfold NTypes.goodPar NTypes.goodTuple goodSig
  simp only [D.ntypes.labPar_def, h1]

theorem param_of_Z (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (h41 : SumRepresentations.Conclusion41 D)
    (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i) (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) :
    ∃ Sig, IsBCV D.nd D.naut i PI
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  obtain ⟨P0, hP0, Pa0, hB0, hm⟩ := (D.Z_tie i x).1 hx
  obtain ⟨Pa, hB⟩ := h1 i PI
  have hperm : Pa0.Perm Pa := ((h41 i).2.1 P0 PI (by rw [hP0]; exact Option.some_ne_none x)
    (hP0.trans hPI.symm)).1 Pa0 Pa hB0 hB
  have hm' := hperm.subset hm
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm'
  set m : Part D.naut.CG := ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ with hmdef
  have hperm2 : (l₁ ++ m :: l₂).Perm ((l₁ ++ l₂) ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hB' := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm2 hB
  have hL : ∀ p ∈ l₁ ++ l₂, 1 ≤ p.a := fun p hp => (hB.1 p (by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  refine ⟨twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT, ?_⟩
  have e : twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
      D.naut.etaTinv = (l₁ ++ l₂) ++ [m] := by
    rw [show twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
        D.naut.etaTinv = twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT) D.naut.etaTinv ++
          twistIso D.nd D.naut [muPart D.nd D.naut i] D.naut.etaTinv from List.map_append ..,
      twistIso_eta D h0.1 h5.1 _ hL]
    rfl
  rw [e]
  exact hB'

theorem eigen_action_at_good_point (D : D7) (Q : PairedCharacterCondition.Pend D) (hSer : GlobalTheory.TypeLeaf.SerLoc D) (h41 : SumRepresentations.Conclusion41 D)
    (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i)
    (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) :
    (x ∈ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
    (x ∉ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := by
  have hon : ∀ σ' : D.ntypes.Par, F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' →
      (D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
      (¬ D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := fun σ' hF' =>
    idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => hSer i σ' k v f F hF' hf
  have hmem : ∀ Sig (σ' : D.ntypes.Par), (∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w) →
      IsBCV D.nd D.naut i PI (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) →
      F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
    intro Sig σ' hσ hB
    have hle : D.naut.typeV i PI ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
      rw [D.mtpar_tie i σ']
      exact le_iSup₂_of_le PI ⟨Sig, fun w => (hσ w).symm, hB⟩ le_rfl
    exact hle hF
  constructor
  · intro hg
    obtain ⟨-, Sig, ⟨P2, hP2, hB2⟩, hgs⟩ := (D.Zgood_tie i x).1 hg
    obtain ⟨Pa, hB⟩ := h1 i PI
    have hperm := ((h41 i).2.1 P2 PI (by rw [hP2]; exact Option.some_ne_none x)
      (hP2.trans hPI.symm)).1 _ Pa hB2 hB
    have hBPI := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨P2, hP2, hB2⟩
    exact (hon σ' (hmem Sig σ' hσ hBPI)).1 ((goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).2 hgs)
  · intro hg
    obtain ⟨Sig, hB⟩ := param_of_Z D h0 h1 h5 h41 i x hx PI hPI
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨PI, hPI, hB⟩
    refine (hon σ' (hmem Sig σ' hσ hB)).2 fun hgp => hg ?_
    rw [D.Zgood_tie i x]
    exact ⟨(D.Z_tie i x).1 hx, Sig, ⟨PI, hPI, hB⟩, (goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).1 hgp⟩

theorem main : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D →
    SumRepresentations.Conclusion41 D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  intro D Q hEig hCen hSer h41 _ h0 h1 h5 i _ _
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  have hact : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
    intro F
    rw [hz]
    unfold NTypes.onMt
    rw [dif_pos (Subalgebra.smul_mem _ hcen _), dif_pos hcen, ← LinearMap.smul_apply, ← map_smul]
    rfl
  refine ⟨Q.zO i z, Q.zO_comm i z, ?_, ?_⟩
  · intro x hx u hu
    have hZ : x ∈ D.nd.Z i := (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
    have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
      rw [hact, (eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x hZ PI hPI F hF).1 hx, map_natCast]) u hu
    rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
  · intro x hx hxg u hu
    have := hEig i z x 0 (fun PI hPI F hF => by
      rw [hact, (eigen_action_at_good_point D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg, smul_zero, map_zero, zero_smul]) u hu
    rw [this, zero_smul]

end GlobalTheory.PassOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExpone
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.LengthH0Bound

theorem toNat_div_le (A B : ℕ∞) (r c : ℕ) (h : A ≤ (r : ℕ∞) * (c : ℕ∞) * B) :
    ((A.toNat : ℚ) / (B.toNat : ℚ)) ≤ (r : ℚ) * c := by
  rcases eq_or_ne B ⊤ with hB | hB
  · rw [hB, ENat.toNat_top, Nat.cast_zero, div_zero]; positivity
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB
  have h' : A ≤ ((r * c * b : ℕ) : ℕ∞) := by push_cast; exact h
  obtain ⟨a, ha, hle⟩ := ENat.le_natCast_iff.mp h'
  subst ha
  rw [ENat.toNat_coe, ENat.toNat_coe]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.cast_zero, div_zero]; positivity
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast hle

theorem lenUnit_le_of_kill {O : Type} [CommRing O] [IsDomain O] (k p c : ℕ)
    (hp : algebraMap O (FractionRing O) (p : O) ≠ 0) (W : Submodule O (KOG O k))
    (hW : ∀ x ∈ W, (p : O) ^ c • x = 0) :
    lenUnit (O := O) p ↥W ≤ (k : ℚ) * c := by
  have hlen := length_le_of_killed (LL := FractionRing O) (stdG O (FractionRing O) k) _
    (GlobalTheory.FiniteTwistInvariants.stdG_eq_span k) (p : O) hp c W hW
  exact toNat_div_le _ _ k c hlen

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem locM_entry {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (i j : Fin k) :
    Br.locM Bw M g i j = Br.toLLK Bw (algebraMap O (FractionRing O) (M (Br.ι Bw g) i j)) := by
  rw [Br.toLLK_alg]; rfl

theorem vecS_mulVec' {k : ℕ} (M : ↥Gw →* Matrix (Fin k) (Fin k) O)
    (g : ↥(GK Bw.Kw)) (u : Fin k → FractionRing O) :
    Br.vecS Bw k ((mapM (algebraMap O (FractionRing O)) M (Br.ι Bw g)).mulVec u) =
      (Br.locM Bw M g).mulVec (Br.vecS Bw k u) := by
  funext i
  change Br.toLLK Bw (∑ j, algebraMap O (FractionRing O) (M (Br.ι Bw g) i j) * u j) =
    ∑ j, Br.locM Bw M g i j * Br.toLLK Bw (u j)
  simp only [map_sum, map_mul, locM_entry]

set_option synthInstance.maxHeartbeats 400000 in

theorem phi_eq_zero {k : ℕ} (z : KOG O k) (hz : Br.phi Bw k z = 0) : z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change (Submodule.Quotient.mk (Br.vecS Bw k y) :
    (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) = 0 at hz
  rw [Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨b, hb⟩ := hz
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨fun j => Bw.eO.symm (b j), funext fun j => ?_⟩
  apply (Br.toLLK Bw).injective
  have hbj := congrFun hb j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply] at hbj ⊢
  rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  exact hbj

set_option synthInstance.maxHeartbeats 400000 in

theorem actD_phi {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ)
    (gK : ↥(GK Bw.Kw)) (x : KOG O k) :
    actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k ((WKG M).comp f (Br.ι Bw gK) x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := vecS_mulVec' Bw (M.comp f) gK y
  change (Submodule.Quotient.mk (((Br.locM Bw (M.comp f)) gK).mulVec (Br.vecS Bw k y)) :
      (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k) =
    Submodule.Quotient.mk (Br.vecS Bw k
      (((mapM (algebraMap O (FractionRing O)) (M.comp f)) (Br.ι Bw gK)).mulVec y))
  rw [h]

set_option synthInstance.maxHeartbeats 400000 in

theorem inv_killed {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (f : ↥Gw →* Γ) (p c : ℕ)
    (h : ∀ y : (Fin k → Br.LLw Bw) ⧸ stdG (Br.Ow Bw) (Br.LLw Bw) k,
      (∀ gK, actD (Br.lat Bw (M.comp f)) gK y = y) → ((p : Br.Ow Bw) ^ c) • y = 0) :
    ∀ x ∈ Representation.invariants ((WKG M).comp f), (p : O) ^ c • x = 0 := by
  intro x hx
  have hfix : ∀ gK, actD (Br.lat Bw (M.comp f)) gK (Br.phi Bw k x) = Br.phi Bw k x := by
    intro gK
    rw [actD_phi, hx (Br.ι Bw gK)]
  have hk := h _ hfix
  apply phi_eq_zero Bw
  rw [LinearMap.map_smulₛₗ]
  simp only [map_pow, map_natCast]
  exact hk

include Bw in

theorem natCast_ne_zero : algebraMap O (FractionRing O) ((l : ℕ) : O) ≠ 0 := by
  intro h
  have h2 := congrArg (Br.toLLK Bw) h
  rw [map_natCast, map_natCast, map_zero] at h2
  have hQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  apply hQ
  apply (algebraMap ℚ_[l] (Br.LLw Bw)).injective
  rw [map_natCast, map_zero]
  exact h2

end Bridge

set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
    (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) (c : ℕ),
    let S := LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs;
    ∀ T : LocLat S.G S.Qp S.LL S.O, T = GlobalTheory.HubX.wLat D i ρ π u hu hc →
    (∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ c) • x = 0) →
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * c := by
  intro D HW i ρ π u hu s hs hc c S T hT hkill
  subst hT
  have hp : LocalSituation.ell S = D.nd.l i := (D.loc (D.nd.l i)).PD_p _
  have hK := inv_killed (D.nbr i u hu) (WpO D.nd i ρ π) (decS D.nd u) (D.nd.l i) c (fun y hy => by
    have := hkill y hy
    rwa [hp] at this)
  have hq := lenUnit_le_of_kill D.R.r (D.nd.l i) c (natCast_ne_zero (D.nbr i u hu)) _ hK
  exact_mod_cast hq

end GlobalTheory.LengthH0Bound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaAboveDetOne
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_above_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ,
      ∫⁻ g in 𝓕 ∩ {g | 1 ≤ GlobalTheory.RSnm.detAbs g}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  first | (exact @GlobalTheory.SBThetaUpper.lintegral_theta_upper_ne_top) | (exact GlobalTheory.SBThetaUpper.lintegral_theta_upper_ne_top) | (intros; apply GlobalTheory.SBThetaUpper.lintegral_theta_upper_ne_top  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaBelowDetOne
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_below_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ, 1 < x →
      ∫⁻ g in 𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  first | (exact @GlobalTheory.ThetaSqLow.lintegral_low_ne_top) | (exact GlobalTheory.ThetaSqLow.lintegral_low_ne_top) | (intros; apply GlobalTheory.ThetaSqLow.lintegral_low_ne_top  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogCardLevelGroupLeScalePowMulLength
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem log_card_levelGroup_le_scale_pow_mul_length : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ C * x ^ C * (Fm.L x i).sc.L := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.log_levelGroup_le_and_level_large eps Fm
  refine ⟨15, max x0 1, fun x hx hx1 i => ?_⟩
  have h := (hx0 x (le_trans (le_max_left _ _) hx) hx1 i).1
  have h1x : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hL : 1 ≤ (Fm.L x i).sc.L := Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hp : (0 : ℝ) ≤ x ^ (15 : ℝ) := Real.rpow_nonneg (by linarith) _
  unfold Formalism.BasicNotions.lam0 at h
  calc Real.log ((Fm.D x i).what₂.restRowsFiniteGroupCard : ℝ) ≤ x ^ (15 : ℝ) := h
    _ ≤ 15 * x ^ (15 : ℝ) := by linarith
    _ = 15 * x ^ (15 : ℝ) * 1 := by ring
    _ ≤ 15 * x ^ (15 : ℝ) * (Fm.L x i).sc.L := by gcongr

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialCoeffGoodOfCuspidal
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_coeff_good_of_cuspidal : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    Good (GlobalTheory.StdCharConductor.psi E) m (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  first | (exact @GlobalTheory.PartialBlock.good_partialCoeff_blockGL) | (exact GlobalTheory.PartialBlock.good_partialCoeff_blockGL) | (intros; apply GlobalTheory.PartialBlock.good_partialCoeff_blockGL  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticZetaNeOneAtPlace
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.QuadAtQ

theorem main : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), GlobalTheory.NFacts.Facts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1 := by
  intro D L nch i r π ρ fa _ _ hHG hr _ _ v hv
  exact ⟨fun x _ γ hγ => ((galois_condition_five_of D i r fa.Conclusion2.1 hHG hr v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ,
    ((GlobalTheory.TameDesign.main D i).2 v (Or.inr hv)).2.2.1 hv⟩

end GlobalTheory.QuadAtQ
end

