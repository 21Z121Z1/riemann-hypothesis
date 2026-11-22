import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0314
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDuality
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.CrZero

theorem pow_cancel {A : Type*} [CommRing A] (p : A) (hp : ∀ x : A, p * x = 0 → x = 0)
    (k : ℕ) (a b : A) (h : p ^ k * a = p ^ k * b) : a = b := by
  induction k generalizing a b with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have h' : p * (p ^ k * a - p ^ k * b) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
    exact sub_eq_zero.mp (hp _ h')

theorem eq_zero_of_forall_dvd {A : Type*} [CommRing A] (p : A)
    (hH : IsHausdorff (Ideal.span {p}) A) (x : A) (h : ∀ M : ℕ, p ^ M ∣ x) : x = 0 := by
  refine hH.haus x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr (h n)

end GlobalTheory.CrZero

open GlobalTheory.CrZero in

theorem GlobalTheory.BKLim.acris_frob_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d c : ℕ)
    (D₀ F F' : Matrix (Fin d) (Fin d) (Per.Acris l)),
    (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D₀ i j) →
    (l : Per.Acris l) ^ c • D₀ = F * D₀.map (phiA l) * F' → D₀ = 0 := by
  intro l _ K bk d c D₀ F F' hdiv hfr
  obtain ⟨htor, hcomp, -, hphi, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp

  have key : ∀ n : ℕ, ∃ N : Matrix (Fin d) (Fin d) (Per.Acris l),
      (l : Per.Acris l) ^ (c * n) • D₀ = u ^ (l ^ n) • N := by
    intro n
    induction n with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv i j).choose, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [one_mul]; exact (hdiv i j).choose_spec
    | succ n ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨F * N.map (phiA l) * F', ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)
          = (l : Per.Acris l) ^ (c * n) • D₀.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ n) • N).map (phiA l) = u ^ (l ^ (n + 1)) • N.map (phiA l) := by
        ext i j; simp [hφu, ← pow_mul]; ring
      calc (l : Per.Acris l) ^ (c * (n + 1)) • D₀
          = (l : Per.Acris l) ^ (c * n) • ((l : Per.Acris l) ^ c • D₀) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)) * F' := by
            rw [hfr, hmap, Matrix.mul_smul, Matrix.smul_mul]
        _ = u ^ (l ^ (n + 1)) • (F * N.map (phiA l) * F') := by
            rw [hN, hmap2, Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  have hH : IsHausdorff (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) := hcomp.toIsHausdorff
  refine eq_zero_of_forall_dvd _ hH _ fun M => ?_
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually l K bk c M
  obtain ⟨N, hN⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D₀ i j = u ^ (l ^ n₀) * N i j := by
    have := congrFun (congrFun hN i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j, ?_⟩
  apply pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValLeOfNotMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.TwoBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem addVal_le_of_notMem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l x : O}
    (hx : x ∉ Ideal.span {l} * IsLocalRing.maximalIdeal O) :
    IsDiscreteValuationRing.addVal O x ≤ IsDiscreteValuationRing.addVal O l := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 hlt.le
  by_cases hy : IsUnit y
  · rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hy, add_zero] at hlt
    exact lt_irrefl _ hlt
  · exact hx (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self l) hy)

noncomputable def bound (w e r k : ℕ) : ℕ := Nat.rec w (fun _ b => 2 * (e + 1) * b + 2 + 2 * r) k

theorem bound_succ (w e r k : ℕ) : bound w e r (k + 1) = 2 * (e + 1) * bound w e r k + 2 + 2 * r := rfl

theorem bound_step (w e r k : ℕ) : bound w e r k + 1 + 2 * r ≤ bound w e r (k + 1) := by
  rw [bound_succ]; nlinarith [Nat.zero_le (e * bound w e r k)]

theorem bound_mono (w e r : ℕ) : Monotone (bound w e r) :=
  monotone_nat_of_le_succ fun k => le_trans (by omega) (bound_step w e r k)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i} {M R n : ℕ} {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}

theorem NF_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NF bkP i s M d P c) :
    NF bkP i s M d P c' := fun Q hQ a Φ hΦ F hF =>
  (h Q hQ a Φ hΦ F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩

theorem NFit_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NFit bkP i s M d P c) :
    NFit bkP i s M d P c' := fun Q hQ a Φ hΦ =>
  (h Q hQ a Φ hΦ).imp id fun ⟨b, b', hb⟩ => ⟨b, b', fun F hF => (hb F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩⟩

theorem induct (hl : 0 < nu X i) {t R₀ : ℕ} (f : Fin t → X.Sig i) (hG : ∀ j, Grow bkP i (f j)) (hS : ∀ j, Step bkP i (f j))
    {H : Subgroup (GE N)} {S A : Finset (PlE D.host)} {L : Subgroup (GE N)} {z : GE N} {w e : ℕ}
    (he : IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e)
    (hM : bound w e D.R.r t ≤ X.l i ^ (M - nu X i - 1)) (h3 : nu X i + 2 ≤ M)
    (hd : AdmFam X i M H S d) (hLH : L ≤ H) (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : ∀ j, Small2 i (f j) M L z)
    (P₀ : Fin (R₀ + t) ⊕ Fin R₀ → PlE D.host) (h₀ : PiLocalization₂ i M d A L z P₀) (hF : ∀ j, NFit bkP i (f j) M d P₀ (w + 1)) :
    ∀ k, k ≤ t → ∃ P : Fin (R₀ + t) ⊕ Fin (R₀ + k) → PlE D.host, (∀ a, P (.inl a) = P₀ (.inl a)) ∧ PiLocalization₂ i M d A L z P ∧
      (∀ j, NFit bkP i (f j) M d P (bound w e D.R.r k + 1)) ∧
      ∀ j : Fin t, j.val < k → NF bkP i (f j) M d P (bound w e D.R.r k + 1) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨P₀, fun _ => rfl, h₀, hF, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨P, hP, hSt, hFit, hNF⟩ := ih (by omega)
    have hb : bound w e D.R.r (k + 1) ≤ X.l i ^ (M - nu X i - 1) := (bound_mono w e D.R.r hk).trans hM
    have hs := bound_step w e D.R.r k
    obtain ⟨P', hE, hSt', hN⟩ := hS ⟨k, hk⟩ hl M (R₀ + t) (R₀ + k) H S d A L z P (bound w e D.R.r k) e (by omega) he hb h3
      hd hLH hz (hL _) hSt (hFit _)
    have hg := fun j => hG j hl M (R₀ + t) (R₀ + k) d A L z P P' (bound w e D.R.r k + 1) (by omega) (hs.trans hb) h3 hz
      (hL j) hSt' hE
    refine ⟨P', fun a => (hE (.inl a)).trans (hP a), hSt', fun j => NFit_mono (by omega) ((hg j).2 (hFit j)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact NF_mono (by omega) ((hg j).1 (hNF j hj))
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      exact NF_mono (Nat.le_succ _) hN

theorem thmC_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → Start bkP i s ∧ Grow bkP i s ∧ Step bkP i s) → ThmC bkP := by
  intro D N X bkP hAB hCh hP i hl T hT
  obtain ⟨R₀, hR⟩ := hCh i T hT
  have : Finite (X.Sig i) := (X.finSig i).finite
  obtain ⟨t, f, -, hf⟩ := (Set.toFinite T).fin_param
  have hfT : ∀ j, f j ∈ T := fun j => hf ▸ Set.mem_range_self j
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hl0 : (X.l i : X.O0 i) ≠ 0 := fun h0 => by
    have h1 : (X.emb0 i) (X.l i : D.LL0) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (X.O0 i) (FractionRing (X.O0 i))), h0, map_zero]
    exact hp.ne_zero (Nat.cast_eq_zero.1 ((map_eq_zero _).1 h1))
  obtain ⟨e, he⟩ : ∃ e : ℕ, IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e := by
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 (mt IsDiscreteValuationRing.addVal_eq_top_iff.1 (pow_ne_zero (nu X i) hl0))
    exact ⟨e, he.symm⟩
  refine ⟨R₀ + t, bound (4 * D.R.r * R₀) e D.R.r t, bound (4 * D.R.r * R₀) e D.R.r t + nu X i + 3,
    fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hw : 4 * D.R.r * R₀ ≤ bound (4 * D.R.r * R₀) e D.R.r t := bound_mono (4 * D.R.r * R₀) e D.R.r (Nat.zero_le t)
  have hlt : 4 * D.R.r * R₀ + 2 < X.l i ^ M := lt_of_le_of_lt (by omega) (Nat.lt_pow_self (n := M) hp.one_lt)
  have hle : bound (4 * D.R.r * R₀) e D.R.r t ≤ X.l i ^ (M - nu X i - 1) :=
    le_trans (by omega) (Nat.lt_pow_self (n := M - nu X i - 1) hp.one_lt).le
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, hLi⟩ := GlobalTheory.ResSel.SmallSub.exists_small D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  have hh' : ∀ a, Fin.append h (fun _ : Fin t => (1 : GE N)) a ∈ L := fun a => by
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [Fin.append_left]; exact hh a
    · rw [Fin.append_right]; exact L.one_mem
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A (R₀ + t)
    (Fin.append h fun _ => 1) (fun a => ⟨hLH (hh' a), hLζ _ (hh' a)⟩)
  choose φ g hφ hg using hFr
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh' a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hinj : Function.Injective (Sum.map id (Fin.castAdd t) : Fin (R₀ + t) ⊕ Fin R₀ → Fin (R₀ + t) ⊕ Fin (R₀ + t)) :=
    Function.injective_id.sumMap (Fin.castAdd_injective _ _)
  have h₀ : PiLocalization₂ i M d A L z (fun q : Fin (R₀ + t) ⊕ Fin R₀ => P (Sum.map id (Fin.castAdd t) q)) := by
    refine ⟨⟨fun q => hAux.1 _, fun q q' hq => hinj (hAux.2.1 _ _ hq), fun q => hAux.2.2 _⟩,
      fun a => ⟨fun v hv B hB => (hIne _ v hv B hB).trans hUL', fun σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hUL' hg⟩,
      fun a => ⟨dec_le_of_frob_mem (N.plOm.2 _) (hφ (Fin.castAdd t a)) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL _), fun b σ hσ => ?_⟩⟩
    have := hSt.2 (Fin.castAdd t a) b σ hσ
    simpa [Fin.ext_iff] using this
  have hc := hco (fun a => φ (Fin.castAdd t a)) (fun a => GlobalTheory.TwistDet.cConj X (φ (Fin.castAdd t a)))
    (fun a => ⟨hcj _, g (Fin.castAdd t a), by simpa using (hg (Fin.castAdd t a)).1⟩)
  rw [if_neg hl.ne'] at hc
  obtain ⟨P', hP', hSt', -, hNF⟩ := induct hl f (fun j => (hP i _ (hT _ (hfT j))).2.1) (fun j => (hP i _ (hT _ (hfT j))).2.2)
    he hle (by omega) hd hLH hz (fun j => ⟨hLs _ (hfT j), hLζ, hLi _ (hfT j)⟩) _ h₀
    (fun j => (hP i _ (hT _ (hfT j))).1 M (R₀ + t) R₀ d A L z _ _ _ (Nat.le_add_right _ _) hlt hz (hLs _ (hfT j)) h₀
      (fun a => ⟨hφ _, hcj _⟩) (hc _ (hfT j))) t le_rfl
  refine ⟨P', hSt'.1, ⟨fun a σ hσ => ?_, fun a b σ hσ => ?_⟩, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  · rw [hP' a] at hσ
    exact (hSt.1 a σ hσ).imp fun _ hg => hg.2
  · simpa [Fin.ext_iff] using (hSt'.2.2 a).2 b σ hσ
  · obtain ⟨j, rfl⟩ : s ∈ Set.range f := hf ▸ hs
    obtain ⟨m, hm, hu⟩ := hNF j j.2 Q hQ a Φ hΦ F hF
    exact ⟨m, Nat.lt_succ_iff.1 hm, addVal_le_of_notMem hu⟩

end GlobalTheory.StepTwo.TwoBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionRegularAndTorsionBounded
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ComplLD

theorem smodEq_iff {Q : Type} [CommRing Q] (I : Ideal Q) (n : ℕ) (x y : Q) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule Q Q)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem eq_zero_of_mem {Q : Type} [CommRing Q] (I : Ideal Q) [IsHausdorff I Q] (x : Q)
    (h : ∀ n, x ∈ I ^ n) : x = 0 :=
  IsHausdorff.haus' x fun n => (smodEq_iff I n x 0).2 (by simpa using h n)

theorem exists_lim {Q : Type} [CommRing Q] (I : Ideal Q) [IsPrecomplete I Q] (f : ℕ → Q)
    (h : ∀ m n, m ≤ n → f n - f m ∈ I ^ m) : ∃ z, ∀ n, f n - z ∈ I ^ n := by
  obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := I) f fun {m n} hmn =>
    (smodEq_iff I m _ _).2 (by rw [show f m - f n = -(f n - f m) by ring]; exact neg_mem (h m n hmn))
  exact ⟨z, fun n => (smodEq_iff I n _ _).1 (hz n)⟩

theorem regular_and_torsion_bounded : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (d : L) (N : ℕ), d ∈ nonZeroDivisors L → (∀ (x : L) (m : ℕ), (l : L) ^ m * x ∈ Ideal.span {d} → (l : L) ^ N * x ∈ Ideal.span {d}) → IsCompl i (Ideal.span {(l : L)} ⊔ Ideal.span {d}) → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  intro l _ L _ Q _ i d N hd hbd hc
  set J : Ideal L := Ideal.span {(l : L)} ⊔ Ideal.span {d} with hJ
  set I : Ideal Q := J.map i with hI
  haveI : IsAdicComplete I Q := hc.complete
  have hpow : ∀ n, (J ^ n).map i = I ^ n := fun n => Ideal.map_pow _ _ _
  have surj : ∀ (x : Q) n, ∃ a, x - i a ∈ I ^ n := fun x n => by
    obtain ⟨a, ha⟩ := hc.surj x n; exact ⟨a, by rwa [← hpow]⟩
  have ker : ∀ a n, i a ∈ I ^ n → a ∈ J ^ n := fun a n h => hc.ker a n (by rwa [hpow])
  have strict : ∀ n z, i d * z ∈ I ^ (2 * (n + N + 1)) → z ∈ I ^ n := by
    intro n z hz
    obtain ⟨a, ha⟩ := surj z (2 * (n + N + 1))
    have h1 : i (d * a) ∈ I ^ (2 * (n + N + 1)) := by
      have e : i (d * a) = i d * z - i d * (z - i a) := by rw [map_mul]; ring
      rw [e]; exact sub_mem hz (Ideal.mul_mem_left _ _ ha)
    have h2 := GlobalTheory.T.mem_pow_of_mul_mem_pow_bounded_torsion l L d N hd hbd n a (ker _ _ h1)
    have h3 : i a ∈ I ^ n := by rw [← hpow]; exact Ideal.mem_map_of_mem i h2
    have h4 : z - i a ∈ I ^ n := Ideal.pow_le_pow_right (by omega) ha
    simpa using add_mem h4 h3
  have reg : i d ∈ nonZeroDivisors Q := by
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z hz => eq_zero_of_mem I z fun n => strict n z (by rw [hz]; exact zero_mem _),
      fun z hz => eq_zero_of_mem I z fun n => strict n z (by rw [mul_comm (i d) z, hz]; exact zero_mem _)⟩
  have closed : ∀ x, (∀ n, ∃ z, x - i d * z ∈ I ^ n) → x ∈ Ideal.span {i d} := by
    intro x hx
    choose z hz using fun n => hx (2 * (n + N + 1))
    obtain ⟨w, hw⟩ := exists_lim I z fun m n hmn => strict m _ (by
      have e : i d * (z n - z m) = (x - i d * z m) - (x - i d * z n) := by ring
      rw [e]; exact sub_mem (hz m) (Ideal.pow_le_pow_right (by omega) (hz n)))
    have h0 : x - i d * w = 0 := eq_zero_of_mem I _ fun n => by
      have e : x - i d * w = (x - i d * z n) + i d * (z n - w) := by ring
      rw [e]; exact add_mem (Ideal.pow_le_pow_right (by omega) (hz n)) (Ideal.mul_mem_left _ _ (hw n))
    exact Ideal.mem_span_singleton'.2 ⟨w, by rw [mul_comm]; exact (sub_eq_zero.1 h0).symm⟩
  refine ⟨reg, fun x m hx => closed _ fun n => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨a, ha⟩ := surj x (m + n + 1)
  obtain ⟨b, hb⟩ := surj y (m + n + 1)
  have h1 : i ((l : L) ^ m * a - d * b) ∈ I ^ (m + n + 1) := by
    have e : i ((l : L) ^ m * a - d * b) = -((l : Q) ^ m * (x - i a)) + i d * (y - i b) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_natCast]; linear_combination (-1 : Q) * hy
    rw [e]; exact add_mem (neg_mem (Ideal.mul_mem_left _ _ ha)) (Ideal.mul_mem_left _ _ hb)
  have h2 : (l : L) ^ m * a - d * b ∈ Ideal.span {(l : L) ^ (m + n)} ⊔ Ideal.span {d} := by
    have hle : J ^ (m + n + 1) ≤ Ideal.span {(l : L)} ^ (m + n) ⊔ Ideal.span {d} ^ 1 :=
      Ideal.sup_pow_add_le_pow_sup_pow
    simpa [Ideal.span_singleton_pow] using hle (ker _ _ h1)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h2
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  have h3 : (l : L) ^ m * (a - (l : L) ^ n * c) ∈ Ideal.span {d} :=
    Ideal.mem_span_singleton'.2 ⟨b + e, by linear_combination huv⟩
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 (hbd _ _ h3)
  refine ⟨i f, ?_⟩
  have hf' := congrArg i hf
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf'
  have e : (l : Q) ^ N * x - i d * i f = (l : Q) ^ N * (x - i a) + i ((l : L) ^ (N + n) * c) := by
    rw [map_mul, map_pow, map_natCast]; linear_combination (-1 : Q) * hf'
  rw [e]
  refine add_mem (Ideal.pow_le_pow_right (by omega) (Ideal.mul_mem_left _ _ ha)) ?_
  rw [← hpow]
  refine Ideal.mem_map_of_mem i (Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega : n ≤ N + n)
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) (N + n))))

end GlobalTheory.BSP.ComplLD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Adm8AtOfUnramifiedHeckeStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HkFrob i s → characterTwistExists D.ntw D.nexp i s := by
  first | exact @GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob | exact GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob | (intros; apply GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisationStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_shape_and_epsilon_at_every_localisation : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible (D := D) i ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  first | exact @GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main | exact GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main | (intros; apply GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ ι : Type, Nonempty (TopBasis bk.ev bk.J ι) := by
  first | exact @GlobalTheory.BSP.AinfTopBasis.main | exact GlobalTheory.BSP.AinfTopBasis.main | (intros; apply GlobalTheory.BSP.AinfTopBasis.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimePropertiesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_envelope_mod_prime_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)), (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) * x = 0 → x = 0) ∧ (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) ∣ En.inl.f (bk.ev X) * x → ((l : ℕ) : En.Q.A) ∣ x) ∧ ∀ x : En.Q.A, (∀ m : ℕ, ∃ z, ((l : ℕ) : En.Q.A) ∣ x - En.inl.f (bk.ev X) ^ m * z) → ((l : ℕ) : En.Q.A) ∣ x := by
  first | exact @GlobalTheory.BSP.env_ainf_mod | exact GlobalTheory.BSP.env_ainf_mod | (intros; apply GlobalTheory.BSP.env_ainf_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicCharacterOfAdmStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_character_of_adm : ∀ D : D7, SumRepresentations.adm2 D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D := by
  first | exact @GlobalTheory.AlgCharFromGal.main | exact GlobalTheory.AlgCharFromGal.main | (intros; apply GlobalTheory.AlgCharFromGal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularSurjectionsOfFontaineTheorem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TiedRegular

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem regular_onto (h : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) :
    (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
    (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
    ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  refine ⟨fun K b hb hg => ?_, fun u => ?_, fun K w => ?_⟩
  · have hu : IsUnit (T.eB b) := by
      refine h.regular C K (T.eB b) (fun h0 => hb (T.eB.injective (h0.trans (map_zero _).symm))) fun g hgK => ?_
      obtain ⟨x, hx⟩ := hg g hgK
      refine ⟨x, ?_⟩
      rw [← T.actB, hx, Algebra.smul_def, map_mul,
        IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, hC.u]
      rfl
    simpa using hu.map T.eB.symm
  · obtain ⟨x, hx⟩ := GlobalTheory.Published.FontaineBcris.oneSubPhiOnto_of_filZero (h.ontoFilZero C) (T.eB u)
    refine ⟨T.eB.symm x, T.eB.injective ?_⟩
    rw [map_sub, T.frob, RingEquiv.apply_symm_apply, hx]
  · obtain ⟨x, hx, hF⟩ := h.fundOnto C (T.eD w)
    refine ⟨T.eB.symm x, T.eB.injective ?_, ?_⟩
    · rw [T.frob, RingEquiv.apply_symm_apply, hx]
    · rw [T.fil, map_sub, hC.ι, RingEquiv.apply_symm_apply]
      exact hF

end GlobalTheory.MemLoc.TiedRegular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFactsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdR_filtration_ker_theta_generator_facts : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → (∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n}) ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a) ∧ (∀ (n : ℕ) (z : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n ↔ z ∈ Per.FilP l n) ∧ (∀ x : Per.BdR l, ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ))) ∧ (∀ (a : ℤ) (n : ℕ) (x : Per.BdR l), algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ n * x ∈ Per.FilD l (a + n) ↔ x ∈ Per.FilD l a) ∧ Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  first | exact @GlobalTheory.MemLoc.seed_fil | exact GlobalTheory.MemLoc.seed_fil | (intros; apply GlobalTheory.MemLoc.seed_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDualityStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_annihilator_of_integralLocalDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.IntegralDuality (P.PD K) → bkBCore (P.PD K) := by
  first | exact @GlobalTheory.BKIntDescent.bkBCore_of_integralDuality | exact GlobalTheory.BKIntDescent.bkBCore_of_integralDuality | (intros; apply GlobalTheory.BKIntDescent.bkBCore_of_integralDuality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCharactersTypePrimeProof
section
noncomputable section

namespace GlobalTheory.Pass.HfCharStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem main : StepHfChar := fun D _ HW F h hI i _ _ h2 w hw h1 =>
  GlobalTheory.HfCharProof.hfChar D HW F h hI i w hw h2 ((IntermediateField.finrank_eq_one_iff.mp h1).le.trans bot_le)

end GlobalTheory.Pass.HfCharStep

end
end

