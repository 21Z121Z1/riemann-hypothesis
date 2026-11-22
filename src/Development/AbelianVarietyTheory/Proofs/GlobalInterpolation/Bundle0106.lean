import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0095
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0099
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.MuOffMove

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem ordDet_congr {E : Type} [Field E] [NumberField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {N₁ N₂ : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal N₁ = localization₂ P.asIdeal N₂) : ordDet P N₁ = ordDet P N₂ := by
  unfold ordDet frameAt
  rw [h]

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

theorem natCast_mem_under (Q : HeightOneSpectrum (𝓞 X.E)) (p : ℕ) :
    ((p : ℕ) : 𝓞 X.F) ∈ Q.asIdeal.under (𝓞 X.F) ↔ ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal := by
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem level_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (Pr.T u : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩
  · exact notMem_of_mem_QE hsel h (hPr.T_prime u) hS

theorem mem_vT (hPr : Pr.Ok) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal := by
  have h0 : Pr.piT u ≠ 0 := by
    refine left_ne_zero_of_mul (b := X.conjO (Pr.piT u)) ?_
    rw [hPr.piT_norm u]
    exact_mod_cast (hPr.T_prime u).ne_zero
  refine ⟨decoFin_mem_of_mem_divs, fun h => ?_⟩
  unfold Primes.vT divs
  have hf : {P : HeightOneSpectrum (𝓞 X.E) | Pr.piT u ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {Pr.piT u}) (by simpa using h0)).subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  rw [dif_pos hf]
  simpa using h

theorem conjP_notMem_vT (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u) : conjPrime₂ P ∉ Pr.vT u :=
  fun h => conj_piT_notMem hPr u ⟨P, hP⟩ ((mem_conjP _ _).1 ((mem_vT hPr u _).1 h))

open Classical in

def term (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

theorem term_finite (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (Function.mulSupport (term sel SB mU N)).Finite := by
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  refine ((GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.preimage hinj.injOn).subset fun v hv h0 => hv ?_
  unfold term
  split_ifs
  · rfl
  · rw [h0, zpow_zero, Units.val_one]

open Classical in
theorem term_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ} (hU : ∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) {n : ℕ}
    {N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)} (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (hA : AgreeOff (Pr.T u) N₁ N₂)
    (v : HeightOneSpectrum (𝓞 X.F)) :
    term sel (rowSG Pr sel mu) mU N₁ v =
      (∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * term sel (rowSG Pr sel mu) mU N₂ v := by
  by_cases hv : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v
  · obtain ⟨P, hP, hPv⟩ := hv
    have hPv' : P.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hPv
    have hc := conjP_notMem_vT hPr hP
    have hsp := (split_of_conj_ne₂ X P v hX (fun e => hc (e.symm ▸ hP)) hPv').2
    have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = {P} := by
      ext Q
      rw [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun ⟨hQ, hQv⟩ => ?_, fun e => e ▸ ⟨hP, hPv⟩⟩
      exact ((hsp Q).1 (congrArg HeightOneSpectrum.asIdeal hQv)).resolve_right fun e => hc (e ▸ hQ)
    have hno : ¬ ∃ Q ∈ rowSG Pr sel mu, Q.asIdeal.under (𝓞 X.F) = v.asIdeal := by
      rintro ⟨Q, hQ, hQv⟩
      refine level_notMem_rowSG hPr hsel hS hQ ?_
      rw [← natCast_mem_under, hQv, ← hPv', natCast_mem_under]
      exact T_mem hPr u ⟨P, hP⟩
    unfold term
    rw [hfil, Finset.prod_singleton, if_neg hno, if_neg hno, ← Units.val_mul]
    congr 1
    unfold idxExp
    rcases (hsp (sel v)).1 (hsel v) with e | e
    · rw [e, ← zpow_add]
      congr 1
      ring
    · rw [e, hU P hP, GlobalTheory.OrdDetConj.ordDet_conjP h₁, GlobalTheory.OrdDetConj.ordDet_conjP h₂, inv_zpow', inv_zpow', ← zpow_add]
      congr 1
      ring
  · have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun Q hQ e => hv ⟨Q, hQ, e⟩
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
      intro h
      rw [← hPr.piT_norm u] at h
      rcases (sel v).isPrime.mem_or_mem h with h | h
      · exact hv ⟨sel v, (mem_vT hPr u _).2 h, HeightOneSpectrum.ext (hsel v)⟩
      · exact hv ⟨conjPrime₂ (sel v), (mem_vT hPr u _).2 ((mem_conjP _ _).2 h),
          HeightOneSpectrum.ext ((under_conjP hX _).trans (hsel v))⟩
    unfold term
    rw [hfil, Finset.prod_empty, one_mul, ordDet_congr (hA _ hT)]

theorem muOff_move : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (n : ℕ) (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → (∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) → IsSdLat N₁ → IsSdLat N₂ → AgreeOff (Pr.T u) N₁ N₂ → muOff sel (rowSG Pr sel mu) mU N₁ = (∏ P ∈ Pr.vT u, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * muOff sel (rowSG Pr sel mu) mU N₂ := by
  intro X Pr sel S mu u mU n N₁ N₂ hX hPr hsel hS _ hU h₁ h₂ hA
  classical
  change ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₁ v = _ * ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₂ v
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 X.F) =>
      ∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) ⊆
      ((Pr.vT u).image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    by_contra hn
    apply hv
    refine Finset.prod_eq_one fun P hP => absurd ?_ hn
    rw [Finset.mem_filter] at hP
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, hP.1, hP.2⟩)
  rw [finprod_congr (term_eq (mu := mu) hX hPr hsel hS hU h₁ h₂ hA),
    finprod_mul_distrib ((Finset.finite_toSet _).subset hsub) (term_finite hsel _ mU h₂),
    finprod_eq_prod_of_mulSupport_subset _ hsub,
    Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]

end GlobalTheory.MuOffMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingNonvanishingIffEventuallyNonzero
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.QNormal

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section General

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem IntHom.comp {a b c : ℕ} {x : (Fin b → E) →ₗ[E] (Fin c → E)} {y : (Fin a → E) →ₗ[E] (Fin b → E)}
    (hx : IntHom P x) (hy : IntHom P y) : IntHom P (x ∘ₗ y) := fun v hv => hx _ (hy v hv)

theorem IntHom.pow_mono {a b : ℕ} {x : (Fin a → E) →ₗ[E] (Fin b → E)} {N N' : ℕ} (h : N ≤ N')
    (hx : IntHom P (((qOf P : E) ^ N) • x)) : IntHom P (((qOf P : E) ^ N') • x) :=
  fun v hv l => Proof.NormalFormAtPrime.intAt_pow_mono h (hx v hv l)

theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : IntV P (Loc.eN E N i) := by
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem intAt_chArg {n' c' n c : ℕ} {x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)} {u : E} (hx : IntHom P (u • x)) :
    IntAt P (u * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h
  · exact hx _ (intV_eN P _ _) _
  · simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem unfNe_transfer [CharZero K] (hP : IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {n' c' n c : ℕ} (hc : 1 ≤ c) (hc' : c' = c + 1)
    {psi : E → K} {D N : ℕ} (hN : N ≤ D) (hpsi : CharTo P D psi) {Psi Psi' : Loc.SF E K (n' + c') (n + c)}
    (h1 : HomBdd P N Psi) (h2 : HomBdd P N Psi') {C : K} (hC : C ≠ 0)
    {r : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} {r' : (Fin (n' + c') → E) ≃ₗ[E] (Fin (n' + c') → E)}
    (hr : r ∈ Loc.R1 E n c) (hr' : r' ∈ Loc.R1 E n' c')
    (hrel : ∀ x, Psi' x = C * Psi (r.toLinearMap ∘ₗ x ∘ₗ r'.toLinearMap)) (H : UnfNe P psi Psi) : UnfNe P psi Psi' := by
  obtain ⟨A₀, B₀, H⟩ := H
  obtain ⟨xj', hx⟩ := Function.ne_iff.1 (H (max A₀ N) (max B₀ N) (le_max_left _ _) (le_max_left _ _))
  obtain ⟨xj, T, b, hT⟩ := GlobalTheory.T.unipotentRadicals_act_affine_unfoldingSpaces GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions E n' c' n c hc hc' r hr r' hr' xj'
  obtain ⟨d, hd⟩ := GlobalTheory.T.unfoldingCharacterArgument_comp_unipotentRadicals GlobalTheory.T.exists_xx1_eq_iff_inX_eN_Ufl_conditions E n' c' n c hc hc' r hr r' hr'
  have I1 := GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz E K P n' c' n c psi D N Psi hN hpsi h1 xj'
  have I2 := GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz E K P n' c' n c psi D N Psi' hN hpsi h2 xj
  obtain ⟨A₁, B₁, hA⟩ := GlobalTheory.T.boxSum_ne_zero_invariant_affineChange GlobalTheory.T.vectors_linearMaps_bounded_denominators_atPrime GlobalTheory.T.sum_coset_reps_ne_zero_iff_commensurable GlobalTheory.T.rationalFractions_represent_primeNormQuotient E K P hP _ (integrand psi Psi xj') N I1.1 T b
  refine ⟨max A₁ N, max B₁ N, fun A B hA' hB' => Function.ne_iff.2 ⟨xj, ?_⟩⟩
  have h3 : boxSum P A B (integrand psi Psi xj') ≠ 0 := by
    rw [GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz E K P hP.1 _ _ N I1.1 A B (le_of_max_le_right hA') (le_of_max_le_right hB'),
      ← GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz E K P hP.1 _ _ N I1.1 (max A₀ N) (max B₀ N) (le_max_right _ _) (le_max_right _ _)]
    exact hx
  have h4 := (hA A B (le_of_max_le_left hA') (le_of_max_le_left hB')).2 h3
  have hdep : ∀ t, Psi (Loc.xx1 xj' (T t + b)) ≠ 0 → IntAt P ((qOf P : E) ^ D * d) ∧
      IntAt P ((qOf P : E) ^ D * -Loc.chArg (Loc.xx1 xj' (T t + b))) := by
    intro t ht
    have a1 := Proof.NormalFormAtPrime.intAt_pow_mono hN (I1.2 _ ht)
    have a2 := Proof.NormalFormAtPrime.intAt_pow_mono hN (I2.2 t (by rw [hrel, hT]; exact mul_ne_zero hC ht))
    refine ⟨?_, by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a1⟩
    have := a1.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a2)
    rw [← hT, hd] at this
    convert this using 1
    ring
  have hpt : ∀ t, integrand psi Psi' xj t = C * psi d * integrand psi Psi xj' (T t + b) := by
    intro t
    unfold integrand
    rw [hrel, hT]
    by_cases ht : Psi (Loc.xx1 xj' (T t + b)) = 0
    · simp [ht]
    · have e : -Loc.chArg (Loc.xx1 xj t) = d + -Loc.chArg (Loc.xx1 xj' (T t + b)) := by
        rw [← hT, hd]
        ring
      rw [e, hpsi.1 _ _ (hdep t ht).1 (hdep t ht).2]
      ring
  have hd0 : psi d ≠ 0 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h4)
    have a := (hdep t (left_ne_zero_of_mul ht)).1
    have := hpsi.1 d (-d) a (by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a)
    rw [add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)] at this
    exact left_ne_zero_of_mul (this ▸ one_ne_zero)
  change boxSum P A B (integrand psi Psi' xj) ≠ 0
  have e : boxSum P A B (integrand psi Psi' xj) =
      C * psi d * boxSum P A B (fun t => integrand psi Psi xj' (T t + b)) := by
    unfold boxSum
    simp only [hpt, ← Finset.mul_sum]
    ring
  rw [e]
  exact mul_ne_zero (mul_ne_zero hC hd0) h4

theorem homBdd_translate {a b i : ℕ} {Φ Psi : Loc.SF E K a b} {C : K} {g : (Fin a → E) ≃ₗ[E] (Fin a → E)}
    {h : (Fin b → E) ≃ₗ[E] (Fin b → E)} (hΦ : ∀ x, Φ x ≠ 0 → IntHom P x)
    (hΦ' : ∀ x y, IntHom P y → Φ (x + (qOf P : E) • y) = Φ x)
    (g1 : IntHom P g.symm.toLinearMap) (g2 : IntHom P (((qOf P : E) ^ i) • g.toLinearMap))
    (h1 : IntHom P h.symm.toLinearMap) (h2 : IntHom P (((qOf P : E) ^ (i + 1)) • h.toLinearMap))
    (e : ∀ x, Psi x = C * Φ (h.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap)) : HomBdd P (i + 1) Psi := by
  refine ⟨fun x hx v hv => ?_, fun x y hy => ?_⟩
  · rw [e] at hx
    have := h2 _ (hΦ _ (right_ne_zero_of_mul hx) _ (g1 v hv))
    simpa using this
  · rw [e, e, ← hΦ' (h.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ (h1.comp (hy.comp g2))]
    congr 2
    refine LinearMap.ext fun v => ?_
    simp [pow_succ', mul_smul]

end General

section Chain

open IndefiniteRowSideFullHecke.SandwichNormalForm

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def Between (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  IntHom P h.symm.toLinearMap ∧ IntHom P (((qOf P : X.E) ^ j) • h.toLinearMap)

theorem between_iff {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (h : AutY X R j) :
    (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P) ↔ Between j P h := by
  simp only [mem_lamYat hP]
  exact ⟨fun H => ⟨fun v hv => (H v hv).1, fun v hv => (H v hv).2⟩, fun H v hv => ⟨H.1 v hv, H.2 v hv⟩⟩

theorem between_of_nf {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) {h : AutY X R j} (H : NF Pr j P h) :
    Between j P h := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.latticeSandwich_of_latticeNormalForm X Pr R j P hP h 1 H (one_mem _)
  rw [mul_one] at h1 h2
  refine (between_iff hP h).1 fun x hx => ⟨?_, h2 x hx⟩
  obtain ⟨y, hy, rfl⟩ := h1 x hx
  rwa [show h⁻¹ (h y) = y from h.symm_apply_apply y]

theorem sameDC_symm {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h' : AutY X R j}
    (a : SameDC (Pr := Pr) sharp j P h h') : SameDC (Pr := Pr) sharp j P h' h := by
  obtain ⟨r, hr, k, hk, rfl⟩ := a
  exact ⟨r⁻¹, inv_mem hr, k⁻¹, inv_mem hk, by group⟩

theorem sameDC_mul (sharp : Bool) {j : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) {r : AutY X R j}
    (hr : r ∈ Loc.R1 X.E (R.N j) (cOf R j)) : SameDC (Pr := Pr) sharp j P h (r * h) :=
  ⟨r, hr, 1, one_mem _, (mul_one _).symm⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def omScal (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) : X.K :=
  muAt Ch sel mu cst i P (LinearEquiv.det hal : X.Eˣ) * (muAt Ch sel mu cst i P (LinearEquiv.det h : X.Eˣ))⁻¹ *
    cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) (LinearEquiv.det hal : X.Eˣ)) * (R.N (i + 1) + cOf R (i + 1) : ℕ)) *
    cst.sq P ^ (LocE.vP P.1 (qOf P.1) (LinearEquiv.det h : X.Eˣ) * (R.N i + cOf R i : ℕ))

theorem omPhi_eq (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P hal h x =
      omScal Ch sel mu cst i P hal h * PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) := rfl

theorem localUnfoldingNonvanishing_iff_eventuallyNonzero (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) :
    FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ UnfNe P.1 (cst.psi P) (omPhi Ch sel mu cst i P hal h) := Iff.rfl

variable {Ch sel mu cst}

theorem omScal_ne_zero (hc : cst.Ok) {i : ℕ} {P : rowSG Pr sel mu} (hd : DegOne P.1) (hm : cst.muq (i + 1) P ≠ 0)
    (hal : AutY X R i) (h : AutY X R (i + 1)) : omScal Ch sel mu cst i P hal h ≠ 0 := by
  have hq : cst.sq P ≠ 0 := by
    intro e
    have := hc.sq_sq P
    rw [e, zero_pow two_ne_zero] at this
    exact hd.1.ne_zero (by exact_mod_cast this.symm)
  have hmu : ∀ a : X.Eˣ, muAt Ch sel mu cst i P a ≠ 0 := fun a => GlobalTheory.T.localCharacter_ne_zero_of_ne_zero X.E X.K P.1 hd _ _ _ hm a.ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hmu _) (inv_ne_zero (hmu _))) (zpow_ne_zero _ hq)) (zpow_ne_zero _ hq)

theorem rank_le (R : Ranks) (j : ℕ) : R.k ≤ R.N j ∧ R.r ≤ R.N j + cOf R j := by
  have : j ≤ j * (R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold Ranks.N Ranks.r cOf
  omega

theorem phiAt_prop {sharp : Bool} {i : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    (∀ x, PhiAt Ch mu sharp i P x ≠ 0 → IntHom P x) ∧
      ∀ x y, IntHom P y → PhiAt Ch mu sharp i P (x + (qOf P : X.E) • y) = PhiAt Ch mu sharp i P x := by
  unfold PhiAt
  rw [if_neg hP]
  exact GlobalTheory.T.twistPrimeDatum_integral_support_and_invariant X.E X.K P _ _ _ _ _ _ _ (rank_le R i).1 (rank_le R (i + 1)).1 (rank_le R i).2 (rank_le R (i + 1)).2

theorem omPhi_bdd {i : ℕ} {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) {hal : AutY X R i} {h : AutY X R (i + 1)}
    (h1 : Between i P.1 hal) (h2 : Between (i + 1) P.1 h) : HomBdd P.1 (i + 1) (omPhi Ch sel mu cst i P hal h) :=
  homBdd_translate (phiAt_prop hP).1 (phiAt_prop hP).2 h1.1 h1.2 h2.1 h2.2 (omPhi_eq Ch sel mu cst i P hal h)

theorem omPhi_mul {i : ℕ} {P : rowSG Pr sel mu} {hal : AutY X R i} {h : AutY X R (i + 1)}
    (h0 : omScal Ch sel mu cst i P hal h ≠ 0) (ρ' : AutY X R i) (ρ : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P (ρ' * hal) (ρ * h) x =
      omScal Ch sel mu cst i P (ρ' * hal) (ρ * h) / omScal Ch sel mu cst i P hal h *
        omPhi Ch sel mu cst i P hal h ((ρ⁻¹).toLinearMap ∘ₗ x ∘ₗ ρ'.toLinearMap) := by
  rw [omPhi_eq, omPhi_eq, ← mul_assoc, div_mul_cancel₀ _ h0]
  rfl

theorem first_unipotent_class_transfer (hc : cst.Ok) {i : ℕ} (hi : i + 1 ≤ R.m - 2) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hd : DegOne P.1)
    (hm : cst.muq (i + 1) P ≠ 0) (hD : i + 1 ≤ cst.D P) {hal hal' ρ' : AutY X R i} {h h' ρ : AutY X R (i + 1)}
    (hρ' : ρ' ∈ Loc.R1 X.E _ _) (hρ : ρ ∈ Loc.R1 X.E _ _) (e' : hal' = ρ' * hal) (e : h' = ρ * h)
    (a1 : Between i P.1 hal) (a2 : Between i P.1 hal') (b1 : Between (i + 1) P.1 h) (b2 : Between (i + 1) P.1 h')
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal' h' := by
  rw [localUnfoldingNonvanishing_iff_eventuallyNonzero] at H ⊢
  subst e e'
  exact unfNe_transfer hd (by unfold cOf; omega) (by unfold cOf; omega) hD ⟨hc.psi_add P, hc.psi_int P⟩
    (omPhi_bdd hP a1 b1) (omPhi_bdd hP a2 b2)
    (div_ne_zero (omScal_ne_zero hc hd hm _ _) (omScal_ne_zero hc hd hm _ _)) (inv_mem hρ) hρ'
    (omPhi_mul (omScal_ne_zero hc hd hm _ _) ρ' ρ) H

theorem lamYat_coe {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = {v | IntV P v} :=
  Set.ext fun v => mem_lamYat hP v

variable {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end Chain

end GlobalTheory.QNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIff
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.WeylLocOnePlace

theorem rhoVr_inv_coe {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (lam : ι → DomWeight n) (B : GL (Fin n) E) (F : Formalism.L2.DIV.VV K lam) :
    (rhoVr emb lam B⁻¹ F).1 = actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 := by
  have e : (invTrK.comp (embGL emb)) B⁻¹ = (vlBdF emb (fun _ : ι => B))⁻¹ := by
    rw [map_inv]
    rfl
  show (rhoK lam ((invTrK.comp (embGL emb)) B⁻¹) F).1 = _
  rw [e]
  rfl

theorem mem_locW_delAtr_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (lam lam' : ι → DomWeight n), (∀ τ, (lam τ).natW = (lam' τ).natW) → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ (w : Pl.Pl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B → ∀ F : Formalism.L2.DIV.VV K lam, F ∈ locW Pl w (delAtr emb lam M) ↔ MvPolynomial.map σ (rhoVr emb lam B⁻¹ F).1 ∈ vlIntSpan σ Pl w lam' := by
  intro E K ι _ _ _ _ _ _ _ emb σ Pl pw hval n lam lam' hn M hM w B hB F
  have hbas : ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ M)) (vlBdF emb (fun _ : ι => B) τ) := fun τ =>
    pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
      (vl_isBasisAt_tauLat Pl pw hval emb τ w M B hB)
  have hlat : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ M)) := fun τ =>
    du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ M hM)
  have h0 : F ∈ locW Pl w (delAtr emb lam M) ↔ F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) :=
    vl_mem_span_intW_iff Pl pw hval w _ F
  have hmem : F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) ↔
      actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delStd K lam) := by
    have h1 : F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) ↔
        F.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ M)) := Iff.rfl
    rw [h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ hbas).2]
    constructor
    · rintro ⟨G, hG, hGF⟩
      have e : actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 = G := by
        rw [← hGF]
        show actP lam (vlBdF emb (fun _ : ι => B))⁻¹ (actP lam (vlBdF emb (fun _ : ι => B)) G) = G
        rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
      rw [e]
      exact hG
    · intro h
      refine ⟨_, h, ?_⟩
      show actP lam (vlBdF emb (fun _ : ι => B)) (actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1) = F.1
      rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  rw [h0, hmem, rhoVr_inv_coe]
  constructor
  · intro h
    exact vl_map_mem_intSpan Pl pw hval σ w lam lam' hn h
  · intro h
    obtain ⟨G, hG, hGe⟩ := vl_exists_of_mem_intSpan Pl pw hval σ w lam lam' hn h
    have hG' : actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 = G :=
      (MvPolynomial.map_injective σ σ.injective hGe).symm
    rw [hG']
    exact hG

end GlobalTheory.WeylLocOnePlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexCongPre
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.CongIndex

theorem relIndex_congPre (O K : Type) [CommRing O] [IsLocalRing O] [CommRing K] (ι : O →+* K)
    (hι : Function.Injective ι) (n : ℕ) (H : Subgroup (GL (Fin n) (O ⧸ IsLocalRing.maximalIdeal O))) :
    (congPre ι (IsLocalRing.maximalIdeal O) H).relIndex (bc (n := Fin n) ι).range = H.index := by
  have hinj : Function.Injective (bc (n := Fin n) ι) := by
    intro g h e
    apply Units.ext
    ext a b
    apply hι
    exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) a b) e
  have hs : Function.Surjective (redGL (n := Fin n) (IsLocalRing.maximalIdeal O)) :=
    GlobalTheory.MeasTupleEq.map_residue_surjective O n
  unfold congPre
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
    Subgroup.relIndex_top_right, Subgroup.index_comap_of_surjective _ hs]

end GlobalTheory.CongIndex
end

