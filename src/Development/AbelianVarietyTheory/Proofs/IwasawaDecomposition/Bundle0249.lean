import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm

open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes in

theorem weights_of_minors : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  intro D i σ hσ M _
  subst hσ
  have hnr : ∃ s : ℕ, D.R.r + D.R.t = 2 * s := by
    obtain ⟨a, ha⟩ := Formalism.L2.NTheta.odd_r D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    exact ⟨a + b + 1, by omega⟩
  obtain ⟨s, hs⟩ := hnr
  have hsq : (D.R.r : ℚ) + D.R.t = 2 * s := by exact_mod_cast hs
  choose e he using fun τ : D.what₂.Tau => (D.hc τ).e_int i
  choose d hd using fun τ : D.what₂.Tau => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).d_int
  refine ⟨fun τ => -e τ + s, fun τ => -e τ - s, fun τ => -d τ, fun τ => ?_⟩
  have A := GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ
  obtain ⟨hpq, hV⟩ := A.rank
  have hVq : ((Vc D i).rank : ℚ) = 2 * s := by rw [hV, hs]; push_cast; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he, hVq]; push_cast; ring
  · rw [he, hVq]; push_cast; ring
  · have := hd τ
    unfold dShift at this
    push_cast
    rw [← this]
    ring
  · have hen := M.enum τ
    rw [GlobalTheory.ThetaFiresProbe.parAt_fixed] at hen
    obtain ⟨hn, hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ hpq) hen
    intro a
    obtain ⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x) :=
      ⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩
    rw [hx x]
    congr 1
    rcases x with c | c
    · have h1 := A.kap_plus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) = (aP D i τ c : ℤ) + (-e τ + s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) : ℤ) : ℚ) =
            (((aP D i τ c : ℤ) + (-e τ + s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_pos (by simp)]
      simp
    · have h1 := A.kap_minus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) =
          -(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℤ) : ℚ) =
            ((-(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_neg (by simp)]
      have h3 : (Wc D i).rank - 1 - ((Fin.cast hn (finSumFinEquiv (Sum.inr c)) : Fin (Wc D i).rank) : ℕ) =
          qS D i τ - 1 - c := by
        simp only [finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]
        rw [← hn]
        simp only [qS]
        omega
      rw [h3]
  · intro j
    have h1 := A.coef_eq j
    rw [hd] at h1
    have h2 : (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j = thetaWt D i τ j + d τ := by
      exact_mod_cast h1
    rw [h2]
    have hj := j.2
    unfold wtU thetaWt
    simp only [pS, qS] at hpq ⊢
    by_cases c1 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1
    · have ht := D.R.three_m_lt_t
      rw [if_pos c1, if_pos c1, if_neg (by omega)]
      ring
    · rw [if_neg c1, if_neg c1]
      by_cases c2 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1 + D.R.t
      · rw [if_pos c2, if_neg (by omega)]
        ring
      · rw [if_neg c2, if_pos (by omega)]
        have h3 : (Vc D i).rank - 1 - (j : ℕ) = ((Wc D i).sig (tauE D τ)).2 - 1 - (j - (((Wc D i).sig (tauE D τ)).1 + D.R.t)) := by
          omega
        rw [h3]
        ring

end GlobalTheory.JointHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory

namespace GlobalTheory

theorem nonempty_fockData_pair :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s),
      Nonempty (FockData T0 T1 T2) := by
  intro p q r s T0 T1 T2
  obtain ⟨Om, h⟩ := GlobalTheory.T.exists_oscillatorRepresentation_unitaryCover _ _ T0 (GlobalTheory.Mem.Osc.seqFock _)
  exact GlobalTheory.Osc.nonempty_fockData_iff.2 ⟨h.toOsc⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalNegFirstFamilyFrameCartanMoveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalNegFirstFamily_frame_cartan_move : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → frOf hr eT Z ∈ X.dom ∧ IsUnitFr X (frOf hr eT Z) ∧ X.IsOrtho (frOf hr eT Z) ∧ (∀ ρ, IsCartanInv (gramAt D T ρ) (cartZ T X.p0 Z ρ)) ∧ ∀ h : GA D T, IsONeg T X.p0 (mvZ θ h Z) ∧ (∀ ρ, cartZ T X.p0 (mvZ θ h Z) ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * cartZ T X.p0 Z ρ) ∧ (∀ h', mvZ θ (h' * h) Z = mvZ θ h' (mvZ θ h Z)) ∧ (h ∈ GfC T → mvZ θ h Z = Z) ∧ (mvZ θ h Z = Z → h ∈ GfC T) ∧ ∀ Z', IsONeg T X.p0 Z' → ∃ a ∈ GinfC T, Z' = mvZ θ a Z := by
  first | exact @GlobalTheory.OneMapRef.oneg_frames | exact GlobalTheory.OneMapRef.oneg_frames | (intros; apply GlobalTheory.OneMapRef.oneg_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtMatInjective
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob Formalism.MainNotions.S

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

theorem ptEntry_symm : ∀ (bs : List (E × ℕ)) (a b : ℕ), ptEntry bs a b = ptEntry bs b a
  | [], _, _ => by simp [ptEntry]
  | (t, s) :: bs, a, b => by
    rw [ptEntry, ptEntry, ptEntry_symm bs (a - s) (b - s), add_comm a b]
    simp only [and_comm]

theorem ptEntry_row : ∀ (bs : List (E × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ a < (bs.map Prod.snd).sum, ∃ c < (bs.map Prod.snd).sum,
      ptEntry bs a c ≠ 0 ∧ ∀ b, b ≠ c → ptEntry bs a b = 0
  | [], _, a, ha => by simp at ha
  | (t, s) :: bs, h, a, ha => by
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    simp only [List.map_cons, List.sum_cons] at ha ⊢
    by_cases has : a < s
    · refine ⟨s - 1 - a, by omega, ?_, fun b hb => ?_⟩
      · rw [ptEntry, if_pos (by omega), if_pos (by omega)]; exact ht
      · rw [ptEntry]
        split_ifs <;> first | rfl | omega
    · obtain ⟨c, hc, h1, h2⟩ := ptEntry_row bs (fun b hb => h b (by simp [hb])) (a - s) (by omega)
      refine ⟨c + s, by omega, ?_, fun b hb => ?_⟩
      · rw [ptEntry, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]; exact h1
      · rw [ptEntry, if_neg (by omega)]
        split_ifs
        · exact h2 _ (by omega)
        · rfl

theorem ptEntry_inj : ∀ (bs cs : List (E × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (∀ b ∈ cs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    (bs.map Prod.snd).sum = (cs.map Prod.snd).sum →
    (∀ a < (bs.map Prod.snd).sum, ∀ b < (bs.map Prod.snd).sum, ptEntry bs a b = ptEntry cs a b) → bs = cs
  | [], [], _, _, _, _ => rfl
  | [], (t, s) :: cs, _, h, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e this
    omega
  | (t, s) :: bs, [], h, _, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e this
    omega
  | (t, s) :: bs, (t', s') :: cs, h, h', e, k => by
    obtain ⟨ht, hs⟩ : t ≠ 0 ∧ 1 ≤ s := h (t, s) (by simp)
    obtain ⟨-, hs'⟩ : t' ≠ 0 ∧ 1 ≤ s' := h' (t', s') (by simp)
    simp only [List.map_cons, List.sum_cons] at e k
    have k0 := k 0 (by omega) (s - 1) (by omega)
    rw [ptEntry, if_pos (by omega), if_pos (by omega), ptEntry] at k0
    have hss : s = s' ∧ t = t' := by
      split_ifs at k0
      · exact ⟨by omega, k0⟩
      · exact absurd k0 ht
      · omega
      · exact absurd k0 ht
    obtain ⟨rfl, rfl⟩ := hss
    congr 1
    refine ptEntry_inj bs cs (fun b hb => h b (by simp [hb])) (fun b hb => h' b (by simp [hb])) (by omega)
      fun a ha b hb => ?_
    have := k (a + s) (by omega) (b + s) (by omega)
    rwa [ptEntry, ptEntry, if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
      Nat.add_sub_cancel, Nat.add_sub_cancel] at this

theorem ptMat_injective {m : ℕ} : Function.Injective (ptMat : Point E m → Matrix (Fin m) (Fin m) E) := by
  intro w w' h
  refine Subtype.ext (ptEntry_inj _ _ w.2.1 w'.2.1 (w.2.2.trans w'.2.2.symm) fun a ha b hb => ?_)
  rw [w.2.2] at ha hb
  exact congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩

theorem ptMat_monomial {m : ℕ} (w : Point E m) (a : Fin m) :
    ∃ c, ptMat w a c ≠ 0 ∧ (∀ b, b ≠ c → ptMat w a b = 0) ∧ ∀ k, k ≠ a → ptMat w k c = 0 := by
  have row (a : Fin m) : ∃ c, ptMat w a c ≠ 0 ∧ ∀ b, b ≠ c → ptMat w a b = 0 := by
    obtain ⟨c, hc, h1, h2⟩ := ptEntry_row w.1 w.2.1 a (by rw [w.2.2]; exact a.2)
    rw [w.2.2] at hc
    exact ⟨⟨c, hc⟩, h1, fun b hb => h2 b fun e => hb (Fin.ext e)⟩
  have sy (a b : Fin m) : ptMat w a b = ptMat w b a := ptEntry_symm _ _ _
  obtain ⟨c, h1, h2⟩ := row a
  obtain ⟨d, -, h4⟩ := row c
  obtain rfl : a = d := by_contra fun e => h1 ((sy a c).trans (h4 a e))
  exact ⟨c, h1, h2, fun k hk => (sy k c).trans (h4 k hk)⟩

theorem lo_inv {m : ℕ} {l : Matrix (Fin m) (Fin m) E} (hl : IsLo l) : IsLo l⁻¹ := by
  have := up_inv (u := lᵀ) fun i j => ⟨(hl j i).1, fun e => (hl j i).2 e.symm⟩
  rw [← Matrix.transpose_nonsing_inv] at this
  exact fun i j => ⟨(this j i).1, fun e => (this j i).2 e.symm⟩

theorem ptMat_row_le {m : ℕ} {w w' : Point E m} {l u l' u' : Matrix (Fin m) (Fin m) E} (hl : IsLo l) (hu : IsUp u)
    (hl' : IsLo l') (hu' : IsUp u') (e : l * ptMat w * u = l' * ptMat w' * u') {a c c' : Fin m}
    (h1 : ptMat w a c ≠ 0) (h2 : ∀ k, k ≠ a → ptMat w k c = 0) (h3 : ∀ b, b ≠ c' → ptMat w' a b = 0) :
    c' ≤ c ∧ (c' = c → ptMat w a c = ptMat w' a c') := by
  have e2 : l'⁻¹ * l * ptMat w = ptMat w' * (u' * u⁻¹) := by
    have := congrArg (fun W => l'⁻¹ * W * u⁻¹) e
    simp only [Matrix.mul_assoc, up_mul_inv hu, Matrix.mul_one] at this
    rwa [← Matrix.mul_assoc l'⁻¹ l', Matrix.nonsing_inv_mul l' (by simp [lo_det hl']), Matrix.one_mul,
      ← Matrix.mul_assoc] at this
  have hv := up_mul hu' (up_inv hu)
  have e3 := congrFun (congrFun e2 a) c
  rw [Matrix.mul_apply, Matrix.mul_apply (M := ptMat w'),
    Finset.sum_eq_single a (fun k _ hk => by rw [h2 k hk, mul_zero]) (by simp),
    Finset.sum_eq_single c' (fun k _ hk => by rw [h3 k hk, zero_mul]) (by simp),
    (lo_mul (lo_inv hl') hl a a).2 rfl, one_mul] at e3
  exact ⟨not_lt.1 fun h => h1 (by rw [e3, (hv _ _).1 h, mul_zero]),
    fun h => by rw [e3, (hv _ _).2 h, mul_one]⟩

theorem liesAt_unique {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (w w' : Point E (r + 1))
    (h : LiesAt w Z) (h' : LiesAt w' Z) : w = w' := by
  obtain ⟨l, u, hl, hu, e⟩ := h
  obtain ⟨l', u', hl', hu', e'⟩ := h'
  refine ptMat_injective (Matrix.ext fun a b => ?_)
  obtain ⟨c, h1, h2, h3⟩ := ptMat_monomial w a
  obtain ⟨c', k1, k2, k3⟩ := ptMat_monomial w' a
  have p := ptMat_row_le hl hu hl' hu' (e.symm.trans e') h1 h3 k2
  have q := ptMat_row_le hl' hu' hl hu (e'.symm.trans e) k1 k3 h2
  obtain rfl : c' = c := le_antisymm p.1 q.1
  rcases eq_or_ne b c' with rfl | hb
  · exact p.2 rfl
  · rw [h2 b hb, k2 b hb]

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E} {T' : E}
  {P : Matrix (Fin n) (Fin (r + 1)) E}

theorem Term.At.unique {t : Term σ J T' g P} {w w' : Point E (r + 1)} (h : t.At w) (h' : t.At w') : w = w' :=
  liesAt_unique t.Zhat _ _ h h'

end GlobalTheory.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMUMatMove
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjMove

section Ring

variable {A R k : Type} [CommRing A] [CommRing R] [CommRing k] {m n : ℕ}

def adj (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) :
    Matrix (Fin m) (Fin n) R := C * (Matrix.of Z).map φ * B

theorem adj_move (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B Y : Matrix (Fin n) (Fin n) R)
    (u : Matrix (Fin n) (Fin n) A) (h : (u.map φ)ᵀ * B * Y = B) (M : ℕ) (Z Z' w : Fin m → Fin n → A)
    (hZ : ∀ b, u *ᵥ Z' b = Z b + M • w b) : adj φ C B Z' = (adj φ C B Z + M • adj φ C B w) * Y := by
  have e : (Matrix.of Z).map φ + M • (Matrix.of w).map φ = (Matrix.of Z').map φ * (u.map φ)ᵀ := by
    ext b a
    have := congrArg φ (congrFun (hZ b) a)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.add_apply, Pi.smul_apply, map_add, map_nsmul] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, ← this, mul_comm]
  unfold adj
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add, e]
  conv_lhs => rw [← h]
  simp only [Matrix.mul_assoc]

theorem adj_apply (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A)
    (b' : Fin m) (a : Fin n) : adj φ C B Z b' a = ∑ b, C b' b * ∑ j, φ (Z b j) * B j a := by
  unfold adj
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]

theorem red_eq (S : Subring R) (ρ : S →+* k) (M : ℕ) (hM : (M : k) = 0) (X X' W : Matrix (Fin m) (Fin n) R)
    (y : Matrix (Fin n) (Fin n) S) (hX : ∀ i j, X i j ∈ S) (hX' : ∀ i j, X' i j ∈ S) (hW : ∀ i j, W i j ∈ S)
    (h : X' = (X + M • W) * y.map S.subtype) (i : Fin m) (j : Fin n) :
    ρ ⟨X' i j, hX' i j⟩ = ∑ a, ρ ⟨X i a, hX i a⟩ * ρ (y a j) := by
  have e : (⟨X' i j, hX' i j⟩ : S) = ∑ a, (⟨X i a, hX i a⟩ + M • ⟨W i a, hW i a⟩) * y a j := by
    apply Subtype.ext
    simp [h, Matrix.mul_apply]
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_add, map_nsmul, nsmul_eq_mul, hM, zero_mul, add_zero]

def lft (c : R) (P Q : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R := c • (P * Q)

theorem entry_eq {E : Type} [CommRing E] (f : E →+* R) (φ : A →+* R) (c : R) (P : Matrix (Fin m) (Fin m) R)
    (Q : Matrix (Fin m) (Fin m) E) (X : Matrix (Fin m) (Fin n) E) (G : Matrix (Fin n) (Fin n) E)
    (β : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) (h : ∀ b a, f (X b a) = φ (Z b a)) :
    (fun b a => c * (P * (Q * X * G).map f * β) b a) = adj φ (lft c P (Q.map f)) (G.map f * β) Z := by
  have e1 : X.map f = (Matrix.of Z).map φ := Matrix.ext h
  unfold adj lft
  rw [Matrix.smul_mul, Matrix.smul_mul, ← e1, Matrix.map_mul, Matrix.map_mul]
  ext b a
  simp only [Matrix.mul_assoc, Matrix.smul_apply, smul_eq_mul]

theorem unit_rel_ring (S : Subring R) (σ : A →+* A) (s : A →+* R) (J : Matrix (Fin n) (Fin n) A) (u : GL (Fin n) A)
    (β : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ∈ Formalism.UG.UJ σ J)
    (hy : β * Formalism.UG.bc S.subtype y * β⁻¹ = Formalism.UG.bc s u) :
    (u.1.map (s.comp σ))ᵀ * (J.map s * β.1) * y.1.map S.subtype = J.map s * β.1 := by
  have h1 : β * Formalism.UG.bc S.subtype y = Formalism.UG.bc s u * β := by rw [← hy, inv_mul_cancel_right]
  have h2 : β.1 * y.1.map S.subtype = u.1.map s * β.1 := congrArg Units.val h1
  have h4 : (u.1.map σ)ᵀ * J * u.1 = J := hu
  have h5 := congrArg (fun N => Matrix.map N s) h4
  simp only [Matrix.map_mul] at h5
  have h6 : (u.1.map (s.comp σ))ᵀ * J.map s * u.1.map s = J.map s := h5
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h6]

theorem adj_int_ring (S : Subring R) (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (s : Set (Fin n → A)) (La : Type) [Zero La] (v : La → Fin n → A) (v0 : ∀ j, v 0 j = 0)
    (h : ∀ x : Fin m → La, ∀ i j, adj φ C B (fun b => v (x b)) i j ∈ S)
    (hs : ∀ z ∈ s, ∃ t ∈ S, ∃ l, ∀ j, φ (z j) = t * φ (v l j))
    (w : Fin m → Fin n → A) (hw : ∀ b, w b ∈ AddSubgroup.closure s) (b' : Fin m) (a : Fin n) : adj φ C B w b' a ∈ S := by
  rw [adj_apply]
  refine sum_mem fun b _ => ?_
  have key : ∀ z ∈ AddSubgroup.closure s, C b' b * ∑ j, φ (z j) * B j a ∈ S := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, l, hl⟩ := hs z hz
      have h1 := h (Pi.single b l) b' a
      rw [adj_apply, Finset.sum_eq_single b] at h1
      · have h2 := mul_mem ht h1
        rw [Pi.single_eq_same, mul_left_comm, Finset.mul_sum] at h2
        simpa only [hl, mul_assoc] using h2
      · intro c _ hc
        rw [Pi.single_eq_of_ne hc]
        simp [v0]
      · simp
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      exact add_mem hx hy
    | neg x _ hx =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
      exact neg_mem hx
  exact key _ (hw b)

end Ring

variable {D : D7}

noncomputable def barSwap (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Lev.swapAE D).comp (sigR (Af D.host.F) D.sp.cm.sig)

theorem barSwap_tmul (a : Af D.host.F) (x : D.host.E) :
    barSwap D (a ⊗ₜ[D.host.F] x) = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * barSwap D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) := by
  change D.sp.cm.sig x ⊗ₜ[D.host.F] a = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * (D.sp.cm.sig x ⊗ₜ[D.host.F] 1)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem uMat_eq (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X : Fin S.rank → Fin T.rank → D.host.E) :
    uMat S T βS βT e X = adj (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D)))
      (T.gram.map (eToEAf D) * βT.1) fun b => finVec T (X b) :=
  entry_eq (eToEAf D) (barSwap D) _ _ _ _ _ _ _ fun _ _ => rfl

theorem unit_rel (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (u : GA D T)
    (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (hy : frGL βT y = Lev.finE T u) :
    ((finHom T u).1.map (barSwap D))ᵀ * (T.gram.map (eToEAf D) * βT.1) * y.1.map (Subring.subtype _) =
      T.gram.map (eToEAf D) * βT.1 :=
  unit_rel_ring _ (sigR (Af D.host.F) D.sp.cm.sig) (Lev.swapAE D) (JR (Af D.host.F) T.gram) (finHom T u) βT y
    (GlobalTheory.UnitarySplit.finHom_mem T u) hy

theorem adj_int {m : ℕ} (T : HSp D) (C : Matrix (Fin m) (Fin m) (EAf D)) (B : Matrix (Fin T.rank) (Fin T.rank) (EAf D))
    (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E))
    (h : ∀ x : Fin m → La, IsIntM (adj (barSwap D) C B fun b => finVec T (ι (x b))))
    (w : Fin m → Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : ∀ b, w b ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι)) : IsIntM (adj (barSwap D) C B w) := by
  refine adj_int_ring _ (barSwap D) C B _ La (fun l => finVec T (ι l)) (fun j => ?_) h ?_ w hw
  · show (1 : Af D.host.F) ⊗ₜ[D.host.F] (ι 0 j) = 0
    rw [LinearMap.map_zero]
    exact TensorProduct.tmul_zero _ _
  · rintro z ⟨α, hα, _, ⟨l, rfl⟩, rfl⟩
    exact ⟨(1 : D.host.E) ⊗ₜ[D.host.F] α, Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩), l,
      fun j => barSwap_tmul α (ι l j)⟩

set_option maxHeartbeats 800000 in

theorem redM_uMat_move : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (u : GA D T) (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), frGL βT y = Lev.finE T u → ∀ (M : ℕ) (PP : Pl D.host.E), (M : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x x' : Fin S.rank → La, (∀ b, ∃ w ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι), (finHom T u).1.mulVec (finVec T (ι (x' b))) = finVec T (ι (x b)) + M • w) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) * y.1.map (resS D.host.F PP) := by
  intro D S T βS βT e La _ _ ι hint u y hy M PP hM x x' hx
  choose w hw hx using hx
  have hW := adj_int T _ _ La ι (fun x => by rw [← uMat_eq S T βS βT e]; exact hint x) w hw
  have hmv := adj_move (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D))) _ _ _ (unit_rel T βT u y hy) M
    (fun b => finVec T (ι (x b))) (fun b => finVec T (ι (x' b))) w hx
  rw [← uMat_eq S T βS βT e, ← uMat_eq S T βS βT e] at hmv
  have hM' : (M : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hM
  ext i j
  have := red_eq _ (resS D.host.F PP) M hM' _ _ _ y.1 (hint x) (hint x') hW hmv i j
  rw [Matrix.mul_apply]
  unfold redM
  rw [dif_pos (hint x' i j), this]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dif_pos (hint x i a)]
  rfl

end GlobalTheory.AdjMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerIntertwiner_injective_schwartzBruhat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → e * cA D e = 0 → infPart D e = 0 → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → f₀ ≠ 0 → IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → Φ ≠ 0 → Tm Φ ≠ 0 := by
  first | exact @GlobalTheory.PlaceModelInj.placeModel_ne_zero | exact GlobalTheory.PlaceModelInj.placeModel_ne_zero | (intros; apply GlobalTheory.PlaceModelInj.placeModel_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumnsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_vector_pairs_integral_frame_columns : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ v : Fin W.rank → D.host.E, finVec W v ∈ gLat W 1 → ∀ a : Fin W.rank, ∑ k, eToEAf D (∑ l, D.sp.cm.sig (v l) * W.gram l k) * β.val k a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.PairIntegral.pair_mem_intAf | exact GlobalTheory.PairIntegral.pair_mem_intAf | (intros; apply GlobalTheory.PairIntegral.pair_mem_intAf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormSumLieWordInnerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∃ (m : ℕ) (ls : Fin m → List (Matrix (Fin n) (Fin n) ℂ)) (a : Fin m → H), (∀ i, ∀ X ∈ ls i, X ∈ lieG G) ∧ ∀ w ∈ smSub G (trRep σ P), ℓ w = ∑ i, ⟪a i, word (trRep σ P) (ls i) w⟫_ℂ := by
  first | exact @GlobalTheory.SmVec.sobCont_repr | exact GlobalTheory.SmVec.sobCont_repr | (intros; apply GlobalTheory.SmVec.sobCont_repr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevInequalityAtOneIndefiniteUnitaryStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_inequality_at_one_indefiniteUnitary : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ F : List (Mx n) → Mx n → ℂ, (∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)) → IsDerFam ε F → (∀ l ∈ S, Integrable (fun g : UJ ε => ‖F l (umat g)‖ ^ 2) (muG ε)) → ‖F [] 1‖ ^ 2 ≤ C * (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum := by
  first | exact @GlobalTheory.SobolevHaar.sobolev_at_one | exact GlobalTheory.SobolevHaar.sobolev_at_one | (intros; apply GlobalTheory.SobolevHaar.sobolev_at_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_annihilator_relativelyCompact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ V ∈ nhds (0 : AE D), ∃ C : Set (AE D), IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (a * s)) = 1) → a ∈ C := by
  first | exact @GlobalTheory.SplitAnnihilator.annihilator_subset_compact | exact GlobalTheory.SplitAnnihilator.annihilator_subset_compact | (intros; apply GlobalTheory.SplitAnnihilator.annihilator_subset_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdelicCharacter_localComponent_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1 := by
  first | exact @GlobalTheory.StdCharLocal.psiV_ne_one | exact GlobalTheory.StdCharLocal.psiV_ne_one | (intros; apply GlobalTheory.StdCharLocal.psiV_ne_one <;> assumption)
end

