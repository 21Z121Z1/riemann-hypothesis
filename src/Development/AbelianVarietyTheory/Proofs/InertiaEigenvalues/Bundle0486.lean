import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevOpenNormalIffDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0226
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrime
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhi
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FrobCoord

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem frob_mem_invL_S {f : K⟦X⟧} (hf : f ∈ invL l (S O K e)) : frob K l f ∈ invL l (S O K e) :=
  frob_mem_invL l (fun _ h => frob_mem_S l h) hf

theorem iSl_frob (ϖ : PiSys l e) (f : invL l (S O K e)) :
    ϖ.iSl O K ⟨frob K l f, frob_mem_invL_S f.2⟩ = frobOB l O (ϖ.iSl O K f) := by
  let F : invL l (S O K e) →+* invL l (S O K e) :=
    (frob K l).toRingHom.restrict _ _ fun _ h => frob_mem_invL_S h
  have key : (ϖ.iSl O K).toRingHom.comp F = (frobOB l O).toRingHom.comp (ϖ.iSl O K).toRingHom := by
    have hS : ∀ (x : S O K e) (h : frob K l (x : K⟦X⟧) ∈ invL l (S O K e)) (h' : (x : K⟦X⟧) ∈ invL l (S O K e)),
        ϖ.iSl O K ⟨frob K l x, h⟩ = frobOB l O (ϖ.iSl O K ⟨x, h'⟩) := fun x h h' => by
      rw [ϖ.iSl_of_mem O K (frob_mem_S l x.2) h, ϖ.iSl_of_mem O K x.2 h', ϖ.iS_frob O K x, frobOB_toOB]
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) ?_
    ext x
    exact hS x _ _
  exact RingHom.congr_fun key f

theorem frobOB_idem (t : Wq l a →ₐ[ℤ_[l]] O) (τ : ZMod a) :
    frobOB l O (idem (constB t) τ) = idem (constB t) (τ + 1) := by
  change frobOB l O (toOB l O (toOCr l O (idem (constA t) τ))) = toOB l O (toOCr l O (idem (constA t) (τ + 1)))
  rw [frobOB_toOB, frobOCr_toOCr, frobOA_idem]

theorem iB_frob (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ZMod a → invL l (S O K e)) :
    ϖ.iB t K (fun τ => ⟨frob K l (g (τ - 1)), frob_mem_invL_S (g (τ - 1)).2⟩) = frobOB l O (ϖ.iB t K g) :=
  (map_glue (frobOB l O).toRingHom 1 (frobOB_idem t) fun τ => (iSl_frob ϖ (g (τ - 1))).symm).symm

theorem iB_of_A (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (F : ZMod a → A O K)
    (h : ∀ τ, (F τ : K⟦X⟧) ∈ invL l (S O K e)) :
    ϖ.iB t K (fun τ => ⟨F τ, h τ⟩) = toB l O (ϖ.iTot t K F) :=
  (ϖ.iB_of_mem t K fun τ => ⟨F τ, A_le_S l e (F τ).2⟩).trans (congrArg (toOB l O) (ϖ.iC_of_mem t K F))

theorem toBcris_phi (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ)
    (Y : Matrix ι ι (OA l O)) :
    (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) →
      ∀ m m' : P.MMl, m'.1 = P.phi m.1 →
        toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • toBcris t ϖ P m' =
          (Y.map (frobOA l O)).map (toB l O) *ᵥ fun i => frobOB l O (toBcris t ϖ P m i) := by
  intro hY m m' hm
  choose f hf hYf using hY
  set c := coordL P (invL l (S O K e)) m with hc
  set c' := coordL P (invL l (S O K e)) m' with hc'

  have step1 : ∀ i τ, frob K l (E K l e) ^ α * (c' i τ : K⟦X⟧) =
      ∑ j, (frobAc l (f i j) τ : K⟦X⟧) * frob K l (c j (τ - 1) : K⟦X⟧) := by
    intro i τ
    have h1 : (c' i τ : K⟦X⟧) = frob K l (m.1 (τ - 1) i) := by
      change (P.mxInv τ *ᵥ m'.1 τ) i = _
      rw [hm, PhiMod.phi_apply, Matrix.mulVec_mulVec, P.mxInv_mul_mx, Matrix.one_mulVec, frobV_apply]
    have h2 : m.1 (τ - 1) i = ∑ j, P.mx (τ - 1) i j * (c j (τ - 1) : K⟦X⟧) := by
      rw [← mx_mulVec_coordL P _ m (τ - 1)]
      simp only [Matrix.mulVec, dotProduct, hc]
    rw [h1, h2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coe_frobAc, frobTot_apply, hf i j (τ - 1), map_mul, map_mul, map_pow, mul_assoc]

  let liftA : (ZMod a → A O K) → ZMod a → invL l (S O K e) :=
    fun F τ => ⟨F τ, le_away _ _ (A_le_S l e (F τ).2)⟩
  let cF : ι → ZMod a → invL l (S O K e) :=
    fun j τ => ⟨frob K l (c j (τ - 1)), frob_mem_invL_S (c j (τ - 1)).2⟩
  have step2 : ∀ i, liftA (frobAc l fun _ => EIn l e (A O K)) ^ α * c' i =
      ∑ j, liftA (frobAc l (f i j)) * cF j := by
    intro i
    funext τ
    apply Subtype.ext
    simp only [liftA, cF, Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
      AddSubmonoidClass.coe_finsetSum]
    exact step1 i τ
  ext i
  have h3 := congrArg (ϖ.iB t K) (step2 i)
  rw [map_mul, map_pow, map_sum] at h3
  simp only [Finset.sum_congr rfl fun j _ => map_mul (ϖ.iB t K) (liftA (frobAc l (f i j))) (cF j)] at h3
  simp only [liftA, iB_of_A, cF, iB_frob, ϖ.iTot_frob t K, ϖ.iTot_E t K] at h3
  rw [Pi.smul_apply, smul_eq_mul, toBcris_apply, ← hc', h3]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hYf, toBcris_apply, ← hc]

end GlobalTheory.BKGal.FrobCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatumStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHostDatum_kap_lam0_of_ok : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum | exact GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum | (intros; apply GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem window_cLL_of_jumps_level_one (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (l h r n v : ℕ)
    [CharZero S.Qp] [FiniteDimensional S.Qp S.K] (hl : l.Prime)
    (hcard : Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K) (hn : finrank S.Qp S.K ≤ n) (hr : 1 ≤ r)
    (hv : v ≤ LocalSituation.mN l 1 (h + h) - 1)
    (hU : ∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧
      ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) :
    (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧
      LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) v (LocalSituation.Jset S Y) 0 1 ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  classical
  choose U hUc hUb hUj using hU
  have hpos : 0 < finrank S.Qp S.K := finrank_pos
  have hfin : Finite (S.K →ₐ[S.Qp] S.LL) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (S.K →ₐ[S.Qp] S.LL) := Fintype.ofFinite _
  have hsub : LocalSituation.Jset S Y ⊆ ((Finset.univ.biUnion U : Finset ℤ) : Set ℤ) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := GlobalTheory.HubLoc.jump_of_total S.PD Y.ρ hcard a ha
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hUj τ a hτ⟩)
  have hb : ∀ u ∈ Finset.univ.biUnion U, -(h : ℤ) ≤ u ∧ u ≤ h := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact hUb τ u hτ
  have hc : (Finset.univ.biUnion U).card ≤ n * r := by
    refine (Finset.card_biUnion_le_card_mul _ _ r fun τ _ => hUc τ).trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact hn
  exact ⟨fun a ha => hb a (Finset.mem_coe.1 (hsub ha)),
    GlobalTheory.HubLoc.cLL_unit_interval_le l h (n * r) v _ _ hl (Nat.mul_pos (by omega) hr) hsub hc hb hv⟩

theorem cH0all_le_of_jumps_at_embeddings : ∀ (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hs : Good K 1 LL) (h r n : ℕ) (T : LocLat (LocalSituation.sit LT HW l (AI l) K 1 LL hs).G (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).LL (LocalSituation.sit LT HW l (AI l) K 1 LL hs).O), K.1 ≤ MaximalUnramifiedExtension l → finrank ℚ_[l] ↥K.1 ≤ n → 1 ≤ r → (∀ τ, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧ ∀ a, IsJumpV (LocalSituation.sit LT HW l (AI l) K 1 LL hs).PD T.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ GlobalTheory.HubX.invariantsCountConstant LT HW AI l K 1 LL hs h h T ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  intro LT HW AI l _ K LL hs h r n T hK hn hr hU
  have hl : l.Prime := Fact.out

  have hK1 : K.1 ≤ Ks K 1 := GlobalTheory.HubLoc.le_Ks_one_of_Kur K hK
  have hsplit : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1 := by
    intro τ x
    have e := hs.2.2.2 ((τ.liftNormal (Om l)).comp (Ks K 1).val) ⟨x.1, hK1 x.2⟩
    have e2 : τ.liftNormal (Om l) (algebraMap ↥K.1 (Om l) x) = algebraMap (Om l) (Om l) (τ x) :=
      AlgHom.liftNormal_commutes τ (Om l) x
    have e3 : ((τ.liftNormal (Om l)).comp (Ks K 1).val) ⟨x.1, hK1 x.2⟩ = τ x := e2
    rwa [e3] at e
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := GlobalTheory.HubLoc.card_emb K LL hsplit
  have := K.2
  have hm : 0 < LocalSituation.mN l 1 (h + h) := by unfold LocalSituation.mN; omega
  obtain ⟨h1, h2⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks l K
  have e1 := h1 _ hm
  have e2 := h2 hK
  have hv : padicValNat l (finrank ℚ_[l] ↥(Ks K (LocalSituation.mN l 1 (h + h)))) - padicValNat l (finrank ℚ_[l] ↥K.1) ≤
      LocalSituation.mN l 1 (h + h) - 1 := by omega
  haveI : CharZero (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp := (inferInstance : CharZero ℚ_[l])
  haveI : FiniteDimensional (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).K :=
    (inferInstance : FiniteDimensional ℚ_[l] ↥K.1)
  exact window_cLL_of_jumps_level_one (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T l h r n _ hl hcard hn hr hv hU

end GlobalTheory.HubX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
section
open Formalism.MainNotions.N

namespace GlobalTheory.TraceSemisimple

theorem trace_nondegenerate_of_isSSRep {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ}
    (ρ : Γ →* GL (Fin n) k) (hρ : IsSSRep ρ) (x : Matrix (Fin n) (Fin n) k) (hx : x ∈ spanAlg ρ)
    (htr : ∀ g, (x * ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)).trace = 0) : x = 0 := by
  first
  | (rename_i h_2 h_3 h_4; revert Γ k h_2 h_3 h_4 n ρ hρ x hx htr; exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate)
  | exact @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate
  | (apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SemisimpleTraceForm.trace_form_nondegenerate ..)

theorem isSSRep_mapRep :
    ∀ (Γ k k' : Type) [Group Γ] [Field k] [Field k'] [CharZero k] (ι : k →+* k') (n : ℕ)
      (ρ : Γ →* GL (Fin n) k), IsSSRep ρ → IsSSRep (mapRep ι ρ) := by
  intro Γ k k' _ _ _ _ ι n ρ hρ
  let _ : Algebra k k' := ι.toAlgebra
  have hφι : ∀ (φ : k' →ₗ[k] k) (c : k') (r : k), φ (c * ι r) = φ c * r := by
    intro φ c r
    rw [mul_comm c, mul_comm (φ c), ← smul_eq_mul r, ← map_smul]
    rfl
  have hent : ∀ g i j, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') i j =
      ι (((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) := fun _ _ _ => rfl
  apply isSSRep_of_trace_nondegenerate
  intro x hx htr
  have hmem : ∀ φ : k' →ₗ[k] k, x.map φ ∈ spanAlg ρ := by
    clear htr
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      intro φ
      have : ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k').map φ =
          φ 1 • ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
        ext i j
        rw [Matrix.map_apply, hent, Matrix.smul_apply, smul_eq_mul, ← hφι, one_mul]
      rw [this]
      exact (spanAlg ρ).smul_mem (Submodule.subset_span ⟨g, rfl⟩) _
    | zero =>
      intro φ
      have : (0 : Matrix (Fin n) (Fin n) k').map φ = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add y z _ _ hy hz =>
      intro φ
      have : (y + z).map φ = y.map φ + z.map φ := by ext i j; simp
      rw [this]; exact add_mem (hy φ) (hz φ)
    | smul c y _ hy =>
      intro φ
      exact hy (φ ∘ₗ LinearMap.mulLeft k c)
  have hzero : ∀ φ : k' →ₗ[k] k, x.map φ = 0 := by
    intro φ
    refine trace_nondegenerate_of_isSSRep ρ hρ _ (hmem φ) fun g => ?_
    have := congrArg φ (htr g)
    rw [map_zero] at this
    rw [← this]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, hent, hφι, Matrix.map_apply]
  ext i j
  rw [Matrix.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  exact congrFun (congrFun (hzero φ) i) j

end GlobalTheory.TraceSemisimple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceRankRPartEqTraceBaseChangeTripleStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_rankRPart_eq_trace_baseChangeTriple : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  first | exact @GlobalTheory.TripleTrace.trace_eq | exact GlobalTheory.TripleTrace.trace_eq | (intros; apply GlobalTheory.TripleTrace.trace_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistFrontInputs
section
open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published

namespace GlobalTheory

theorem twist_front_inputs : PoitouTateDuality → LocalFiniteness → LocalTateDuality → LocalFinitenessK → LocalTateDualityK → LocalEulerCharK → GlobalArtinReciprocity → GlobalTheory.TwSys.Cheb ∧ ChebotarevDegreeOne ∧ ChebotarevOpenNormal ∧ PoitouTateTotallyComplex ∧ CohDimTwo ∧ TameLocal ∧ Formalism.MainNotions.BlochKatoReduction.Gen.ArchimedeanSignatureMatching ∧ RayCharacterArtin :=
  fun hP hF hT a b c hA => ⟨cheb_holds, chebotarevDegreeOne', cheb_holds, hP.totallyComplex, ⟨hP.cohDimTwoGlobal, cohDimTwoLocal_of_localFiniteness hF⟩, TameLocal_of_duality hT, (GlobalTheory.TateLimit.twist_cohomology_inputs hP a b c).1, hA.rayCharacterArtin⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem unr_of_iterate_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h →
      ∀ c : P.R.B, P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) →
        ∃ a : ↥(MaximalUnramifiedExtension l), fr l h a = a ∧ c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a := by
  intro l _ P AI T h hh c hc hF
  obtain ⟨E, ω, hEle, hEdim, hEfix, -⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l h hh
  have hK0 : K0 E = E.1 := inf_eq_left.2 hEle
  have hdim : Module.finrank ℚ_[l] ↥(K0 E) = h := by rw [hK0]; exact hEdim
  have hper : Function.IsPeriodicPt (⇑P.φB) h c := hc
  have hall : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD E).Fil 0 := by
    intro j
    have hj : (⇑P.φB)^[j] c = (⇑P.φB)^[j % h] c := by
      conv_lhs => rw [← Nat.mod_add_div j h]
      rw [Function.iterate_add_apply, (hper.mul_const (j / h)).eq]
    have h1 := hF (j % h) (Nat.mod_lt _ hh)
    rw [← SetLike.mem_coe, ← P.PD_Fil _ E 0, hj]
    exact h1
  obtain ⟨a, ha⟩ := GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt l P AI T E c (by rw [hdim]; exact hc) hall
  refine ⟨⟨(a : Om l), a.2.2⟩, ?_, ?_⟩
  · exact (hEfix ⟨(a : Om l), a.2.2⟩).2 a.2.1
  · rw [ha]; rfl

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesNatCombinationApproxStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_natCombination_approx : ∀ (l : ℕ) [Fact l.Prime] (h j d : ℕ) (r : ℝ) (x : Fin d → Fl l) (n : Fin d → ℕ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ a, ‖sh (x a)‖ ≤ r) → ‖sh (∑ a, n a • x a)‖ ≤ r ∧ ‖lam h j (∑ a, n a • x a) - ∑ a, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  first | exact @GlobalTheory.PSer.lamsum | exact GlobalTheory.PSer.lamsum | (intros; apply GlobalTheory.PSer.lamsum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorThreeLayerPropertiesEveryPlaceStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_functor_three_layer_properties_every_place : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; Laws (HW l) (F l) h := by
  first | exact @GlobalTheory.NL.AllLaws.laws | exact GlobalTheory.NL.AllLaws.laws | (intros; apply GlobalTheory.NL.AllLaws.laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelIntersectionFreeOfBaseChange
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.WachKernel

set_option maxHeartbeats 1600000 in

theorem kernel_freeA : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype → FreeA W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π h0 h1 h2 hses hbc
  obtain ⟨hinj, hex, -⟩ := GlobalTheory.EtaleExact.DD_exact D HW F
    (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := (HW l).W_proj K s LL h T₁
  set N₀ := (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)) with hN₀
  haveI : Module.Free W.EE (W.DD T₀) := (W.DD_free T₀).1
  haveI : IsNoetherianRing ↥(OL LL) := inferInstance
  haveI : IsNoetherianRing (PowerSeries ↥(OL LL)) := inferInstance
  haveI : IsNoetherianRing (AA K LL) :=
    inferInstanceAs (IsNoetherianRing (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)))
  haveI : Module.Finite (AA K LL) ↥(W.N T₁) := Module.Finite.iff_fg.mpr (W.N_fg T₁)
  have hfin : Module.Finite (AA K LL) ↥N₀ := by
    let g : ↥N₀ →ₗ[AA K LL] ↥(W.N T₁) :=
      ((W.map ι).restrictScalars (AA K LL)).restrict (fun x hx => hx)
    haveI : IsNoetherian (AA K LL) ↥(W.N T₁) := isNoetherian_of_isNoetherianRing_of_finite _ _
    exact Module.Finite.of_injective g fun a b hab =>
      Subtype.ext (hinj (congrArg Subtype.val hab))
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  have hX : IsSMulRegular ↥N₀ (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) := by
    intro x y hxy
    have h1 : (letπ : AA K LL) • (x : W.DD T₀) = (letπ : AA K LL) • (y : W.DD T₀) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T₀)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  have hreg : ∀ x y : ↥N₀,
      (fun _ => C ((l : ℕ) : ↥(OL LL)) : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • x =
        (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • y →
      ∃ z : ↥N₀, x = (fun _ => X : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → PowerSeries ↥(OL LL)) • z := by
    intro x y hxy
    have hinj : Function.Injective (W.map ι) := hinj
    have hex : Function.Exact (W.map ι) (W.map π) := hex
    let mA := (W.map ι).restrictScalars (AA K LL)
    let x' : ↥(W.N T₁) := ⟨mA x, x.2⟩
    let y' : ↥(W.N T₁) := ⟨mA y, y.2⟩
    have hxy' : (fun _ => C ((l : ℕ) : ↥(OL LL)) : AA K LL) • x' = (fun _ => X : AA K LL) • y' := by
      apply Subtype.ext
      have := congrArg (fun w : ↥N₀ => mA (w : W.DD T₀)) hxy
      simpa only [Submodule.coe_smul, map_smul] using this
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @GlobalTheory.WachFree.mem_X_smul_of_projective ℤ_[l] ↥(W.N T₁) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x' y' (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x' =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y'
        rw [e1, e2]
        exact hxy')
    change x' = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    have hz' : mA x = (fun _ => X : AA K LL) • (z : W.DD T₁) := congrArg Subtype.val hz
    have hπz : W.map π (z : W.DD T₁) = 0 := by
      have h0 : W.map π (mA x) = 0 := (hex _).mpr ⟨(x : W.DD T₀), rfl⟩
      rw [hz'] at h0
      have h0' : (letπ : AA K LL) • W.map π (z : W.DD T₁) = (letπ : AA K LL) • 0 := by
        rw [smul_zero]
        have : W.map π ((letπ : AA K LL) • (z : W.DD T₁)) = (letπ : AA K LL) • W.map π (z : W.DD T₁) :=
          ((W.map π).restrictScalars (AA K LL)).map_smul _ _
        rw [← this]
        exact h0
      rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (0 : W.DD T₂)] at h0'
      exact W.EE_π.smul_left_cancel.mp h0'
    obtain ⟨w, hw⟩ := (hex (z : W.DD T₁)).mp hπz
    have hwN : w ∈ N₀ := by
      show W.map ι w ∈ W.N T₁
      rw [hw]
      exact z.2
    refine ⟨⟨w, hwN⟩, Subtype.ext (hinj ?_)⟩
    change mA x = W.map ι ((fun _ => X : AA K LL) • w)
    rw [hz', ← hw]
    exact (mA.map_smul _ _).symm
  obtain ⟨b⟩ := GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (O := ↥(OL LL)) (N := ↥N₀) (E := W.EE) (D := W.DD T₀) W.EE_inj N₀.subtype hbc
    ((l : ℕ) : ↥(OL LL)) hl0 hl hX hreg
  refine ⟨Module.finrank W.EE (W.DD T₀), fun j => (b j : W.DD T₀), fun j => (b j).2, fun x hx => ?_⟩
  refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_, ?_⟩
  · have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
  · intro a ha
    have hx' : (⟨x, hx⟩ : ↥N₀) = ∑ j, a j • b j :=
      Subtype.ext (by simpa only [Submodule.coe_sum, Submodule.coe_smul] using ha)
    funext j
    rw [hx', b.repr_sum_self]

end GlobalTheory.WachKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_uniqueness_characterisation : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachCharacterisation D HW F := by
  first | exact @GlobalTheory.NL.FrobeniusMatrixUniqueness.main | exact GlobalTheory.NL.FrobeniusMatrixUniqueness.main | (intros; apply GlobalTheory.NL.FrobeniusMatrixUniqueness.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrimeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_good_reduction_at_prime : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBeAt S := by
  first | exact @GlobalTheory.TwistTors.twist_torsion_facts | exact GlobalTheory.TwistTors.twist_torsion_facts | (intros; apply GlobalTheory.TwistTors.twist_torsion_facts <;> assumption)
end

