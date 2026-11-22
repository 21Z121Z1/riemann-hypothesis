import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProof
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes Formalism.L2.NTheta

namespace GlobalTheory.PairWeightArith

lemma toNat_floor_cast {x : ℚ} (hz : ∃ z : ℤ, x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := hz
  have hz : 0 ≤ z := by exact_mod_cast h0
  rw [Int.floor_intCast]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

lemma lamAt_tail {R : Ranks} (h : HCParam R) (n : ℕ) (c : Fin R.m) (hn : n + 1 = R.k + c) :
    lamAt h n = -h.b c := by
  have hk := R.m_add_three_le_k
  have hc := c.2
  unfold lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

lemma lamAt_anti {R : Ranks} (h : HCParam R) {a b : ℕ} (hab : a ≤ b) (hb : b < R.r) :
    lamAt h b + b ≤ lamAt h a + a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have := lamAt_add_add_le h d a hb
  push_cast
  linarith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma sig_eq : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1) := by
  have h := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D τ)
  refine ⟨?_, ?_⟩
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = _
    rw [h]; simp [Ranks.sigW]
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).2 = _
    rw [h]; rfl

lemma pq_eq : pS D i τ + qS D i τ = D.R.r := by
  obtain ⟨h1, h2⟩ := sig_eq D i τ
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  rw [h1, h2]; unfold Ranks.r; omega

lemma t_half : ∃ s : ℕ, (D.R.t : ℚ) = 2 * s + 1 := by
  obtain ⟨s, hs⟩ := D.R.t_odd
  exact ⟨s, by exact_mod_cast hs⟩

lemma aPlusQ_int (a : ℕ) : ∃ z : ℤ, aPlusQ D i τ a = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) a
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨z + e - (pS D i τ : ℕ) + a - s, ?_⟩
  simp only [aPlusQ, centred, eS, hs, hz, he]
  push_cast; ring

lemma neg_dRowQ_int (c : ℕ) : ∃ z : ℤ, -dRowQ D i τ c = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) (pS D i τ + c)
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨-(z + e + c + 1 + s), ?_⟩
  simp only [dRowQ, centred, eS, hs, hz, he]
  push_cast; ring

lemma aPlusQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < pS D i τ) : aPlusQ D i τ b ≤ aPlusQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) hab (by omega)
  simp only [aPlusQ, centred]
  linarith

lemma dRowQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < qS D i τ) : dRowQ D i τ b ≤ dRowQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) (Nat.add_le_add_left hab (pS D i τ)) (by omega)
  simp only [dRowQ, centred]
  push_cast at this
  linarith

lemma one_le_aPlusQ {a : ℕ} (ha : a < pS D i τ) : 1 ≤ aPlusQ D i τ a := by
  obtain ⟨n, hn⟩ : ∃ n, pS D i τ = n + 1 := ⟨pS D i τ - 1, by omega⟩
  refine le_trans ?_ (aPlusQ_anti D i τ (show a ≤ n by omega) (by omega))
  have h1 := lamAt_tail (D.hc τ) n i (by rw [← hn]; exact (sig_eq D i τ).1)
  have g := (D.hc τ).gap_be i
  have hn' : (pS D i τ : ℚ) = n + 1 := by exact_mod_cast hn
  simp only [aPlusQ, centred, eS, h1, hn']
  linarith

lemma one_le_neg_dRowQ {c : ℕ} (hc : c < qS D i τ) : 1 ≤ -dRowQ D i τ c := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have h0 := dRowQ_anti D i τ (Nat.zero_le c) hc
  have hi : (i : ℕ) + 1 < D.R.m := by omega
  have h1 := lamAt_tail (D.hc τ) (pS D i τ + 0) ⟨i + 1, hi⟩ (by simp only; omega)
  have g := (D.hc τ).gap_eb i hi
  have : dRowQ D i τ 0 ≤ -1 := by
    simp only [dRowQ, centred, eS, h1]
    push_cast
    linarith
  linarith

lemma cast_aPlus {a : ℕ} (ha : a < pS D i τ) : (aP D i τ a : ℚ) = aPlusQ D i τ a := by
  unfold aP aPl
  rw [if_pos ha]
  exact toNat_floor_cast (aPlusQ_int D i τ a) (le_trans zero_le_one (one_le_aPlusQ D i τ ha))

lemma aM_cast {c : ℕ} (hc : c < qS D i τ) : (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c := by
  unfold aM aMi
  have e1 : qS D i τ - (qS D i τ - 1 - c) = c + 1 := by omega
  rw [if_pos (by omega), e1, show pS D i τ + (c + 1) - 1 = pS D i τ + c by omega]
  have e2 : -((D.hc τ).e i + lamAt (D.hc τ) (pS D i τ + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2)
      = -dRowQ D i τ c := by
    simp only [dRowQ, centred, eS]; push_cast; ring
  rw [e2]
  exact toNat_floor_cast (neg_dRowQ_int D i τ c) (le_trans zero_le_one (one_le_neg_dRowQ D i τ hc))

lemma aM_cast' {a : ℕ} (ha : a < qS D i τ) : (aM D i τ a : ℚ) = -dRowQ D i τ (qS D i τ - 1 - a) := by
  rw [← aM_cast D i τ (by omega)]
  congr 2
  omega

lemma lam_eq {w : IndefiniteWeightData.WeightData} (hw : IsDataOf D i τ w) {a : ℕ} (ha : a < D.R.r) :
    (w.lam (a + 1) : ℚ) = lamAt (D.hc τ) a := by
  obtain ⟨hk, -, -, -, -, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  unfold Ranks.r at ha
  unfold IndefiniteWeightData.WeightData.lam
  rw [hk]
  by_cases h : a < D.R.k - 1
  · rw [if_pos (by omega)]
    unfold lamAt
    rw [dif_pos h]
    exact hv ⟨a, h⟩
  · rw [if_neg (by omega), lamAt_tail (D.hc τ) a ⟨a + 1 - D.R.k, by omega⟩ (by simp only; omega),
      ← hb, Int.cast_neg]
    congr 3
    simp only; omega

lemma lamPrime_eq (w : IndefiniteWeightData.WeightData) (hw : IsDataOf D i τ w) (a : ℕ) (ha : a < D.R.r + D.R.t) :
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have hr := pq_eq D i τ
  have hl := fun a ha => lam_eq D i τ (a := a) hw ha
  obtain ⟨hk, hm, ht, hj, he, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  have wp : w.p = pS D i τ := by unfold IndefiniteWeightData.WeightData.p; omega
  have wq : w.q = qS D i τ := by unfold IndefiniteWeightData.WeightData.q; omega
  have wn : w.nV = pS D i τ + qS D i τ + D.R.t := by
    unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; unfold Ranks.r at hr; omega
  unfold IndefiniteWeightData.WeightData.lamPrime
  congr 1
  · unfold IndefiniteWeightData.WeightData.thetaWt thetaWt
    rw [wp, wq, ht]
    by_cases h1 : a < pS D i τ
    · rw [if_pos (by omega), if_pos h1, Int.cast_natCast, cast_aPlus D i τ h1]
      unfold IndefiniteWeightData.WeightData.aPlus
      rw [hl a (by omega), wn, wp, wq, he]
      simp only [aPlusQ, centred]
      push_cast; ring
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : a < pS D i τ + D.R.t
      · rw [if_pos (by omega), if_pos h2]; simp
      · rw [if_neg (by omega), if_neg h2]
        obtain ⟨c, rfl⟩ : ∃ c, a = pS D i τ + D.R.t + c := ⟨a - (pS D i τ + D.R.t), by omega⟩
        have hc : c < qS D i τ := by omega
        rw [Nat.add_sub_cancel_left, Int.cast_neg, Int.cast_natCast, aM_cast D i τ hc]
        unfold IndefiniteWeightData.WeightData.aMinus
        have e1 : w.q + 1 - (qS D i τ + 1 - (pS D i τ + D.R.t + c + 1 - pS D i τ - D.R.t)) = c + 1 := by
          omega
        have hi : (i : ℕ) + c + 1 < D.R.m := by omega
        have e2 : (w.b (w.j + (c + 1)) : ℚ) = (D.hc τ).b ⟨i + c + 1, hi⟩ := by
          rw [← hb]; congr 2; simp only; omega
        rw [e1, e2, he, ht]
        simp only [dRowQ, centred]
        rw [lamAt_tail (D.hc τ) (pS D i τ + c) ⟨i + c + 1, hi⟩ (by simp only; omega)]
        push_cast; ring
  · unfold IndefiniteWeightData.WeightData.dTau dShift
    rw [wp, wq, he]

theorem arithAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ := by
  intro D i τ
  have hr := pq_eq D i τ
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hr' : (D.R.r : ℚ) = (pS D i τ : ℚ) + (qS D i τ : ℚ) := by exact_mod_cast hr.symm
  have ho : Odd (pS D i τ + qS D i τ) := hr ▸ odd_r D.R
  have hL := GlobalTheory.ForcedWeights.lamLForced D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 τ
  refine ⟨sig_eq D i τ, ⟨hr, hV⟩, fun a ha => cast_aPlus D i τ ha, fun c hc => aM_cast D i τ hc,
    fun a b hab hb => ?_, fun a b hab hb => ?_, fun a ha => ?_, fun a ha => ?_, fun a => ?_, fun c => ?_, ?_,
    lamPrime_eq D i τ, hL, fun a => ?_⟩
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ hb, cast_aPlus D i τ (by omega)]
    exact aPlusQ_anti D i τ hab hb
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ hb, aM_cast' D i τ (by omega), neg_le_neg_iff]
    exact dRowQ_anti D i τ (by omega) (by omega)
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ ha, Nat.cast_one]
    exact one_le_aPlusQ D i τ ha
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ ha, Nat.cast_one]
    exact one_le_neg_dRowQ D i τ (by omega)
  · rw [kapW_cast _ _ _ ho, cast_aPlus D i τ a.2]
    simp only [kapQ, Sum.elim_inl, aPlusQ, centred, hr']; ring
  · rw [kapW_cast _ _ _ ho, aM_cast D i τ c.2]
    simp only [kapQ, Sum.elim_inr, dRowQ, centred, hr']; ring
  · obtain ⟨s, hs⟩ := ho
    have hs' : (qS D i τ : ℚ) = 2 * s + 1 - pS D i τ := by
      have : (pS D i τ : ℚ) + qS D i τ = 2 * s + 1 := by exact_mod_cast hs
      linarith
    obtain ⟨e, he⟩ := (D.hc τ).e_int i
    refine ⟨(pS D i τ : ℕ) - s - 1 - e, ?_⟩
    simp only [dShift, eS, he, hs']
    push_cast; ring
  · obtain ⟨_, w, hk, hm, ht, hj, he, hv, hb, hw⟩ := hL
    rw [hw a]
    exact lamPrime_eq D i τ w ⟨hk, hm, ht, hj, he, hv, hb⟩ a (hV ▸ a.2)

end GlobalTheory.PairWeightArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoStepPairMeasureFiniteOnCompacts
section
noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

theorem tsfin_compact_lift {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X] (x : X)
    (hc : IsClosed (MulAction.orbit G x)) {K : Set X} (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ y ∈ K, (∃ g : G, g • x = y) → ∃ g ∈ C, g • x = y := by
  haveI : LocallyCompactSpace (MulAction.orbit G x) := hc.locallyCompactSpace
  haveI : ContinuousSMul G (MulAction.orbit G x) :=
    ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  let x₀ : MulAction.orbit G x := ⟨x, MulAction.mem_orbit_self x⟩
  have ho : IsOpenMap fun g : G => g • x₀ := isOpenMap_smul_of_sigmaCompact x₀
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit G x)) :=
    hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let ex := CompactExhaustion.choice G
  obtain ⟨n, hn⟩ := hK'.elim_directed_cover (fun n : ℕ => (fun g : G => g • x₀) '' interior (ex n))
    (fun n => ho _ isOpen_interior)
    (by
      rintro ⟨y, g, rfl⟩ _
      obtain ⟨n, hn⟩ := ex.exists_mem g
      exact Set.mem_iUnion.2 ⟨n + 1, g, ex.subset_interior_succ n hn, rfl⟩)
    (Monotone.directed_le fun a b hab => Set.image_mono (interior_mono (ex.subset hab)))
  refine ⟨ex n, ex.isCompact n, fun y hy hg => ?_⟩
  obtain ⟨g, hg1, hg2⟩ := hn (a := ⟨y, hg⟩) hy
  exact ⟨g, interior_subset hg1, congrArg Subtype.val hg2⟩

theorem tsfin_hform_mulVec {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin n) (Fin n) A)
    (hg : Formalism.UG.cT σ g * J * g = J) (x : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec x) = Formalism.UG.hform σ J x x := by
  have key : ∀ (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A),
      Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ J.mulVec y := by
    intro J x y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : σ ∘ g.mulVec x = (g.map σ).mulVec (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ g x i
  rw [key, key, h2]
  conv_rhs => rw [← hg]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec (M := Formalism.UG.cT σ g), Matrix.dotProduct_mulVec (σ ∘ x),
    Formalism.UG.cT, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tsfin_q_smul (g : HA R σ J) (y : Fin 1 → Fin M → R ⊗[F] E) :
    qR R σ J ((g • y) 0) = qR R σ J (y 0) := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  unfold qR hR
  rw [← tsfin_hform_mulVec _ _ _ hg (y 0)]
  rfl

theorem tsfin_q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin 1 → Fin M → E) (a : F)
    (hx : hE σ J (x 0) (x 0) = algebraMap F E a) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R a := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have h : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      (1 : R) ⊗ₜ[F] algebraMap F E a := by
    rw [← hx]
    simp [hR, hE, Formalism.UG.hform, ratTup, JR, inclR, sigR, TensorProduct.tmul_sum]
  rw [qR, h, qloc_trace_tmul, Algebra.trace_algebraMap, h2, one_mul, ← map_mul]
  congr 1
  simp

theorem tsfin_q_cont [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun y : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (y 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  unfold qR hR Formalism.UG.hform
  fun_prop

end

theorem twoStep_finite_on_compacts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → TwoStep R σ J x B m m' N → IsFiniteMeasureOnCompacts N := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR M J x a B J' m m' N hS hO hm hm' _ hT
  classical
  obtain ⟨hJ, ha, hx, -, hJ', hJ'nd⟩ := hS
  have hq := tsfin_q_rat R σ J hcm.2.2.1 x a hx
  have hu : IsUnit (algebraMap F R a) := (IsUnit.mk0 a ha).map _
  have hc : IsClosed (MulAction.orbit (HA R σ J) (ratTup (F := F) R x)) := by
    have : MulAction.orbit (HA R σ J) (ratTup (F := F) R x) =
        {y | qR R σ J (y 0) = algebraMap F R a} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact (tsfin_q_smul R σ J g _).trans hq
      · intro hy
        exact GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hcm R hR (M + 1) J hJ _ _ y hu hq hy
    rw [this]
    exact isClosed_eq (tsfin_q_cont R σ J) continuous_const
  refine ⟨fun K hK => ?_⟩
  let K₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) := (fun X _ => X 0) '' K
  have hK₁ : IsCompact K₁ := hK.image (by fun_prop)
  obtain ⟨C, hC, hCK⟩ := tsfin_compact_lift _ hc hK₁
  let L : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)
  have hL : L * B = 1 := by
    rw [Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hJ'nd.2)
  have hL' : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  let K' : Set (Fin 1 → Fin M → R ⊗[F] E) :=
    (fun p : HA R σ J × (Fin 2 → Fin (M + 1) → R ⊗[F] E) => fun _ =>
      (L.map (inclR (F := F) R)).mulVec ((p.1⁻¹ • p.2) 1)) '' (C ×ˢ K)
  have hK' : IsCompact K' := (hC.prod hK).image (continuous_pi fun _ =>
    continuous_const.matrix_mulVec ((continuous_apply 1).comp (continuous_fst.inv.smul continuous_snd)))
  let s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J := fun y =>
    if h : ∃ g ∈ C, g • ratTup (F := F) R x = y then h.choose
    else if h' : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h'.choose else 1
  have hs : IsSec R σ J x s := by
    intro y hy
    by_cases h : ∃ g ∈ C, g • ratTup (F := F) R x = y
    · simp only [s, dif_pos h]
      exact h.choose_spec.2
    · simp only [s, dif_neg h, dif_pos hy]
      exact hy.choose_spec
  have hsC : ∀ y ∈ K₁, (∃ g : HA R σ J, g • ratTup (F := F) R x = y) → s y ∈ C := by
    intro y hy hg
    have h := hCK y hy hg
    simp only [s, dif_pos h]
    exact h.choose_spec.1
  have h1 := hT (K.indicator 1) (measurable_one.indicator hK.measurableSet) s hs
  rw [lintegral_indicator_one hK.measurableSet] at h1
  rw [h1]
  have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := hO
  calc _ ≤ ∫⁻ y, K₁.indicator (fun _ => m' K') y ∂m := by
        refine lintegral_mono_ae (hae.mono fun y hy => ?_)
        by_cases hyK : y ∈ K₁
        · rw [Set.indicator_of_mem hyK, ← lintegral_indicator_one hK'.measurableSet]
          refine lintegral_mono fun y' => ?_
          by_cases hp : pairOf R σ J B y (s y) y' ∈ K
          · have : y' ∈ K' := by
              refine ⟨(s y, pairOf R σ J B y (s y) y'), ⟨hsC y hyK hy, hp⟩, ?_⟩
              funext i
              have e : ((s y)⁻¹ • pairOf R σ J B y (s y) y') 1 =
                  ((s y)⁻¹ • s y • fun _ : Fin 1 => (B.map (inclR (F := F) R)).mulVec (y' 0)) 0 := rfl
              simp only
              rw [e, inv_smul_smul, Matrix.mulVec_mulVec, hL', Matrix.one_mulVec,
                Subsingleton.elim i 0]
            simp [Set.indicator_of_mem hp, Set.indicator_of_mem this]
          · simp [Set.indicator_of_notMem hp]
        · have : ∀ y', pairOf R σ J B y (s y) y' ∉ K := fun y' hp =>
            hyK ⟨_, hp, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩
          simp [Set.indicator_of_notMem (this _)]
    _ < ⊤ := by
        rw [lintegral_indicator_const hK₁.measurableSet]
        exact ENNReal.mul_lt_top hK'.measure_lt_top hK₁.measure_lt_top

end GlobalTheory.GaugeEx
end
end

