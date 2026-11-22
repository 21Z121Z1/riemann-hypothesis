import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Formalism.LocalToGlobal.Divisibility.NumbersLink
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedTau1NeRamifiedTau2
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0790
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import GroundTheory.GlobalFields.LocalAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVector
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NatAtStd

theorem isSD_pi (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    IsSDLat E N (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → E, x ∈ (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) ↔
      ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈
      (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

theorem detId_std (D : D7) (N : ℕ) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) = 1 := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    have h : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = A i j := fun i j => by
      have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k _ => by
        by_cases e : k = j
        · subst e
          rw [Pi.single_eq_same]
          exact Submodule.one_le.1 le_rfl
        · rw [Pi.single_eq_of_ne e]
          exact Submodule.zero_mem _
      have h2 := Submodule.mem_one.1 (hA _ h1 i trivial)
      simpa using h2
    choose b hb using h
    have e : A = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix (Matrix.of b) :=
      Matrix.ext fun i j => (hb i j).symm
    rw [e, ← RingHom.map_det]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · exact Submodule.one_le.2 (Submodule.subset_span ⟨1, fun v hv => by simpa using hv, Matrix.det_one.symm⟩)

theorem chi_one (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) : χ 1 = 1 := by
  letI := D.host.cmStar
  have h1 := h.2 1
  rw [Submodule.one_eq_span]
  simpa using h1

theorem chiFac_std (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) (a b : ℕ) :
    Base.chiFac χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = 1 := by
  simp [Base.chiFac, detId_std, chi_one D χ h]

variable (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ}

theorem Iop_self (A : AddSubgroup (TaylorLogMetric.VC D N N')) :
    ∃ x ∈ A, ∀ G : TaylorLogMetric.VC D N N' → ℂ, TaylorLogMetric.Iop D T A A G = fun z => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G z := by
  have htop : A.addSubgroupOf A = ⊤ := AddSubgroup.addSubgroupOf_self A
  haveI hsub : Subsingleton (A ⧸ A.addSubgroupOf A) := by
    rw [htop]; exact QuotientAddGroup.subsingleton_quotient_top
  let q0 : A ⧸ A.addSubgroupOf A := QuotientAddGroup.mk 0
  refine ⟨((Quotient.out q0 : A) : TaylorLogMetric.VC D N N'), Subtype.property _, fun G => ?_⟩
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by rw [htop]; exact AddSubgroup.index_top
  unfold TaylorLogMetric.Iop
  rw [finsum_eq_single _ q0 (fun q hq => absurd (Subsingleton.elim q q0) hq), hi]
  simp

theorem Hf_neg_right (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T z (-x) = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_neg_left (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (-z) x = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_add_left (z w x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (z + w) x = TaylorLogMetric.Hf D T z x + TaylorLogMetric.Hf D T w x := by
  simp [TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, add_div]

theorem al_neg_mul (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x = 1 := by
  unfold TaylorLogMetric.al
  rw [Hf_neg_left, Hf_neg_right, neg_neg, ← mul_zpow]
  simp

theorem inv_op (x : TaylorLogMetric.VC D N N') (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D T (-x) * TaylorLogMetric.U D T (-x) (fun w => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G w) z = G z := by
  have h := al_neg_mul D T x
  unfold TaylorLogMetric.U
  simp only [Hf_add_left, Hf_neg_left, Hf_neg_right, neg_add_cancel_right]
  have he : Complex.exp (-(Real.pi : ℂ) * (TaylorLogMetric.Hf D T z x + -TaylorLogMetric.Hf D T x x) - (Real.pi : ℂ) * TaylorLogMetric.Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * -TaylorLogMetric.Hf D T z x - (Real.pi : ℂ) * - -TaylorLogMetric.Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination (G z) * he * (TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x) + G z * h

theorem eNat_std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → B.VecP χ → ∀ a b : ℕ, Even a → Even b → TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∧ B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = B.thZero a b := by
  intro D cc dl B χ hχ hV a b ha hb
  have hA : TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) := by
    letI := D.host.cmStar
    exact ⟨ha, hb, isSD_pi _ a, isSD_pi _ b⟩
  refine ⟨hA, ?_⟩
  obtain ⟨x, hx, hI⟩ := Iop_self D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b))
  have hTh : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) :=
    (hV a b _ _ hA).1
  have hfix := hTh.2 (-x) (neg_mem hx)
  have he : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = fun z => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x
      (fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w) z := by
    funext z
    unfold Base.eNat Base.thMoved Base.thHalf
    rw [chiFac_std D χ hχ, one_mul, hI, hI]
  have h1 : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) =
      fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w := by
    funext z
    rw [← hfix z]
    conv_lhs => rw [he]
    exact inv_op D B.tor x _ z
  funext z
  rw [← hfix z]
  conv_lhs => rw [h1]
  exact inv_op D B.tor x _ z

end GlobalTheory.NatAtStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumDatumNumbersEqHostOfCompatible
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem logDerivLOne_eq_of_prime_eq (D : D7) (N : NumDatum) (hd : N.d = D.host.d) : N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D := by
  have key : ∀ (a b : ℕ) (ha : a.Prime) (hb : b.Prime), a = b →
      (haveI : Fact a.Prime := ⟨ha⟩
       (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ)) 1).re) =
      (haveI : Fact b.Prime := ⟨hb⟩
       (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod b)).ringHomComp (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((quadraticChar (ZMod b)).ringHomComp (Int.castRingHom ℂ)) 1).re) := by
    rintro a b ha hb rfl
    rfl
  exact key _ _ N.hyp.2.1 D.host.hyp.2.1 hd

theorem numbers_of_hostTie : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X), HostTie N s Pr → N.rd = D.host.rdE ∧ N.v = D.host.v ∧ N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D ∧ N.logOm = TaylorLogMetric.logOmVal D ∧ TaylorLogMetric.fF D = N.R.f ∧ X.f = N.R.f ∧ Module.finrank ℚ X.E = 2 * N.R.f ∧ |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd ∧ TaylorLogMetric.IsCurveIdeal D D.host.ccK := by
  intro D N X s Pr h
  have hrd : N.rd = D.host.rdE := h.rd_eq
  obtain ⟨hR, hq, hd, hcc, -, -, hX, -⟩ := h
  have hv : N.v = D.host.v := by
    rw [NumDatum.v, Host.v, hrd]
  have hL := logDerivLOne_eq_of_prime_eq D N hd
  have hfr : Module.finrank ℚ X.E = Module.finrank ℚ D.host.E :=
    (AlgEquiv.ofRingEquiv (f := s.iE) (fun x => by simp) : X.E ≃ₐ[ℚ] D.host.E).toLinearEquiv.finrank_eq
  have hE : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [hfr, D.host.finrank_E', hR]
  have htower : Module.finrank ℚ X.F * Module.finrank X.F X.E = Module.finrank ℚ X.E :=
    Module.finrank_mul_finrank ℚ X.F X.E
  refine ⟨hrd, hv, hL, ?_, ?_, ?_, hE, ?_, ?_⟩
  · rw [NumDatum.logOm, TaylorLogMetric.logOmVal, hv, hL]
  · rw [TaylorLogMetric.fF, hR]
  · rw [hX.ok.rankE, hE] at htower
    rw [Fields.f, hX.ok.card_Tau]
    omega
  · rw [hrd, Host.rdE, hfr, discr_eq_discr_of_ringEquiv X.E s.iE]
  · rw [hcc]
    refine ⟨top_ne_bot, ?_⟩
    simp

end GlobalTheory.ColNorms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfNumReads
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.NumReads

open Formalism.LatticeIndexTer (ph)

theorem ph_zero : ph 0 = 0 := by simp [ph]

theorem N_pred_le (N : NumDatum) (j : ℕ) (hj : j < N.R.m) : N.R.N ((j + 1) - 1) ≤ N.Nm := by
  unfold NumDatum.Nm Ranks.N
  rw [Nat.add_sub_cancel]
  have := Nat.mul_le_mul_right (N.R.t + 1) hj.le
  omega

theorem ofNum_reads : ∀ (N : NumDatum) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ)
    (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1),
    Reads N eJ δ T (RecNums.ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H) := by
  intro N J _ eJ δ T Nc lam0 C0 ce Ch Sw C1 H
  refine ⟨?_, ?_, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro z
    exact N.mem_topsPl z
  · intro t _
    rfl
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, ph (N.nuPad δ ((eJ j).1 + 1) z i) = _
    unfold NumDatum.nuPad
    have e : ∀ i : Fin N.Nm, ph (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) =
        (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ph ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) := by
      intro i
      split_ifs
      · rfl
      · exact ph_zero
    rw [Finset.sum_congr rfl (fun i _ => e i),
      NumDatum.sum_pad (fun i => ph ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle, Nat.add_sub_cancel]
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, N.nuPad δ ((eJ j).1 + 1) z i = _
    unfold NumDatum.nuPad NumDatum.nuAbs
    rw [NumDatum.sum_pad (fun i => ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle]
    push_cast
    rfl

end GlobalTheory.ColRows.NumReads
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.RamifiedOffD

open Formalism.MainNotions.G GlobalTheory.HCEntries GlobalTheory.FockDegreeGap GlobalTheory.RamifiedLoss

variable {D : D7} {L : SizeData₂ D}

theorem offDiagonalRamified_bound_const_four (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) : Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound D L 4 := by
  intro j hj
  have hp : D.host.d.Prime := D.host.hyp.2.1
  have hb := one_le_b L
  have hL := one_le_scL L
  have hn := one_le_n D
  have hf : (1 : ℝ) ≤ D.R.f := by linarith [f_eq D, one_le_n D]
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hE := abs_EatD_le h P hx j hj
  have hlog : Real.log D.host.d ≤ L.sc.L := by
    obtain ⟨-, -, -, -, -, -, hQ, -⟩ := h
    refine hQ.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_)
    unfold szTh
    linarith [L.sc.eps_pos]
  have hlog0 : 0 ≤ Real.log (D.host.d : ℝ) := Real.log_natCast_nonneg _
  have hE2 : |EatD D j| ≤ 2 * ((D.R.f : ℝ) * L.sc.b) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    have a1 : (D.host.TT.card : ℝ) ≤ D.R.n := by
      rw [← card_HH]
      exact_mod_cast Finset.card_le_univ _
    have a2 : (D.host.TT.card : ℝ) * L.sc.b ≤ D.R.f * L.sc.b :=
      mul_le_mul_of_nonneg_right (by linarith [f_eq D]) (by linarith)
    have a3 : (D.R.f : ℝ) * (D.R.k * L.sc.b') ≤ D.R.f * L.sc.b :=
      mul_le_mul_of_nonneg_left (k_b'_le hS) (by linarith)
    linarith
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0 := by
    rw [hB, show (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L = D.R.m * (D.R.f * L.sc.b * L.sc.L) by ring]
    exact le_mul_of_one_le_left (by positivity) hm
  have h1 : Real.log (D.host.d : ℝ) * |EatD D j| ≤ L.sc.L * (2 * ((D.R.f : ℝ) * L.sc.b)) :=
    mul_le_mul hlog hE2 (abs_nonneg _) (by linarith)
  nlinarith

theorem offDiagonalRamified_bound_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _
  refine ⟨4, 2, by norm_num, fun x hx0 hx i => ?_⟩
  exact offDiagonalRamified_bound_const_four (Fm.sizes x hx i) (Fm.params x hx i) (by rw [Fm.L_x x i hx]; exact hx0)

end GlobalTheory.RamifiedOffD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormAtPairingSqLeOfValueBound
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.PairingOpNorm
open Matrix

theorem pairing_eq {K : Type} [Field K] (c n : ℕ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K))
    (y : Fin c → K) (F : Fin n → K) :
    g y F = F ⬝ᵥ (LinearMap.toMatrix (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g *ᵥ y) := by
  have h := LinearMap.toMatrix_mulVec_repr (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g y
  rw [show (Pi.basisFun K (Fin c)).repr y = y from rfl] at h
  rw [h]
  conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr F]
  simp [dotProduct, map_sum, Basis.dualBasis_repr, mul_comm]

theorem continuous_cnorm {ι : Type} [Fintype ι] : Continuous (Formalism.HermitianLatticesTheory.cnorm : (ι → ℂ) → ℝ) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  fun_prop

theorem cnorm_nonneg {ι : Type} [Fintype ι] (u : ι → ℂ) : 0 ≤ Formalism.HermitianLatticesTheory.cnorm u := Real.sqrt_nonneg _

theorem bilin_bound {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (c n : ℕ)
    (X : Matrix (Fin c) (Fin c) ℂ) (X0 : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin c) ℂ)
    (v : InfinitePlace K) (C : ℝ)
    (h : ∀ (y : Fin c → K) (F : Fin n → K), ‖(fun j => v.embedding (F j)) ⬝ᵥ (S *ᵥ fun i => v.embedding (y i))‖ ≤
      C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ fun j => v.embedding (F j)) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ fun i => v.embedding (y i)))
    (u : Fin n → ℂ) (z : Fin c → ℂ) :
    ‖u ⬝ᵥ (S *ᵥ z)‖ ≤ C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ u) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ z) := by
  have hv : v.IsComplex := IsTotallyComplex.isComplex v
  have hd : DenseRange (Prod.map (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)))
      (Pi.map (fun _ : Fin c => (v.embedding : K → ℂ)))) :=
    DenseRange.prodMap (DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv))
      (DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv))
  have key : ∀ p : (Fin n → ℂ) × (Fin c → ℂ),
      ‖p.1 ⬝ᵥ (S *ᵥ p.2)‖ ≤ C * Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ p.1) * Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ p.2) := by
    intro p
    induction p using hd.induction_on with
    | hp =>
      apply isClosed_le
      · exact (Continuous.dotProduct continuous_fst
          (Continuous.matrix_mulVec continuous_const continuous_snd)).norm
      · exact (continuous_const.mul (continuous_cnorm.comp
          (Continuous.matrix_mulVec continuous_const continuous_fst))).mul
          (continuous_cnorm.comp (Continuous.matrix_mulVec continuous_const continuous_snd))
    | ih q => exact h q.2 q.1
  exact key (u, z)

end GlobalTheory.PairingOpNorm

namespace GlobalTheory.PairingOpNorm
open Matrix

theorem opNormAt_pairing_sq_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (c n : ℕ) (X : InfinitePlace K → Matrix (Fin c) (Fin c) ℂ) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K)) (v : InfinitePlace K) (A : ℝ), IsUnit (X v).det → IsUnit (X0 v).det → (∀ y F, v (g y F) ^ 2 ≤ Real.exp A * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin c)) X v y ^ 2 * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2) → Formalism.HN.opNormAt (Pi.basisFun K (Fin c)) X (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v g ^ 2 ≤ Real.exp A := by
  intro K _ _ _ _ c n X X0 g v A hX hX0 hb
  set σ : K →+* ℂ := v.embedding with hσ
  set S : Matrix (Fin n) (Fin c) ℂ :=
    (LinearMap.toMatrix (Pi.basisFun K (Fin c)) (Pi.basisFun K (Fin n)).dualBasis g).map σ with hS
  set C : ℝ := Real.exp (A / 2) with hC
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hCsq : C ^ 2 = Real.exp A := by rw [hC, sq, ← Real.exp_add]; ring_nf
  have hnorm : ∀ {m : ℕ} (Y : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (x : Fin m → K),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin m)) Y v x = Formalism.HermitianLatticesTheory.cnorm ((Y v)⁻¹ *ᵥ fun i => σ (x i)) := by
    intro m Y x; rfl
  have hK : ∀ (y : Fin c → K) (F : Fin n → K), ‖(fun j => σ (F j)) ⬝ᵥ (S *ᵥ fun i => σ (y i))‖ ≤
      C * Formalism.HermitianLatticesTheory.cnorm ((X0 v)⁻¹ *ᵥ fun j => σ (F j)) * Formalism.HermitianLatticesTheory.cnorm ((X v)⁻¹ *ᵥ fun i => σ (y i)) := by
    intro y F
    have e1 : (fun j => σ (F j)) ⬝ᵥ (S *ᵥ fun i => σ (y i)) = σ (g y F) := by
      rw [pairing_eq, RingHom.map_dotProduct]
      congr 1
      funext i
      exact (RingHom.map_mulVec σ _ y i).symm
    rw [e1, hσ, InfinitePlace.norm_embedding_eq]
    have h1 := hb y F
    rw [hnorm, hnorm] at h1
    have hpos : 0 ≤ C * Formalism.HermitianLatticesTheory.cnorm ((X0 v)⁻¹ *ᵥ fun j => σ (F j)) *
        Formalism.HermitianLatticesTheory.cnorm ((X v)⁻¹ *ᵥ fun i => σ (y i)) :=
      mul_nonneg (mul_nonneg hC0 (cnorm_nonneg _)) (cnorm_nonneg _)
    refine (pow_le_pow_iff_left₀ (apply_nonneg v _) hpos (by norm_num : (2:ℕ) ≠ 0)).1 ?_
    calc v (g y F) ^ 2 ≤ _ := h1
      _ = _ := by rw [mul_pow, mul_pow, hCsq]; ring
  have hB := bilin_bound c n (X v) (X0 v) S v C hK
  have hinv : (Formalism.HN.dualFrame X0 v)⁻¹ = (X0 v)ᵀ := by
    unfold Formalism.HN.dualFrame
    rw [Matrix.nonsing_inv_nonsing_inv]
    rwa [Matrix.det_transpose]
  unfold Formalism.HN.opNormAt
  rw [hinv]
  suffices hT : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((X0 v)ᵀ * S * X v))‖ ≤ C by
    rw [← hCsq]
    exact pow_le_pow_left₀ (norm_nonneg _) hT 2
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 (fun ξ => ?_)
  set M : Matrix (Fin n) (Fin c) ℂ := (X0 v)ᵀ * S * X v with hM
  set w : Fin c → ℂ := WithLp.ofLp ξ with hw
  set m : Fin n → ℂ := M *ᵥ w with hm
  have hTx : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M) ξ‖ = Formalism.HermitianLatticesTheory.cnorm m := by
    simp [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, EuclideanSpace.norm_eq,
      Formalism.HermitianLatticesTheory.cnorm, hm, hw]
  have hξ : ‖ξ‖ = Formalism.HermitianLatticesTheory.cnorm w := by
    simp [EuclideanSpace.norm_eq, Formalism.HermitianLatticesTheory.cnorm, hw]
  rw [hTx, hξ]
  have h1 := hB ((X0 v) *ᵥ star m) ((X v) *ᵥ w)
  have i0 : (X0 v)⁻¹ *ᵥ ((X0 v) *ᵥ star m) = star m := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX0, Matrix.one_mulVec]
  have i1 : (X v)⁻¹ *ᵥ ((X v) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hX, Matrix.one_mulVec]
  rw [i0, i1] at h1
  have e2 : ((X0 v) *ᵥ star m) ⬝ᵥ (S *ᵥ ((X v) *ᵥ w)) = star m ⬝ᵥ m := by
    rw [hm, hM, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsum : 0 ≤ ∑ i, ‖m i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcn : Formalism.HermitianLatticesTheory.cnorm m ^ 2 = ∑ i, ‖m i‖ ^ 2 := by
    unfold Formalism.HermitianLatticesTheory.cnorm; rw [Real.sq_sqrt hsum]
  have e3 : ‖star m ⬝ᵥ m‖ = Formalism.HermitianLatticesTheory.cnorm m ^ 2 := by
    rw [hcn]
    have : star m ⬝ᵥ m = ((∑ i, ‖m i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Complex.star_def, Complex.conj_mul']
    rw [this, Complex.norm_of_nonneg hsum]
  have e4 : Formalism.HermitianLatticesTheory.cnorm (star m) = Formalism.HermitianLatticesTheory.cnorm m := by
    simp [Formalism.HermitianLatticesTheory.cnorm]
  rw [e2, e3, e4] at h1
  rcases (cnorm_nonneg m).eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hC0 (cnorm_nonneg w)
  · refine le_of_mul_le_mul_left ?_ h0
    nlinarith [h1]

end GlobalTheory.PairingOpNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickeningStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicEvaluation_subst_compatible_thickening : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q) (q : Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → HasVal p (fun j => E (u j)) f q → HasVal p z (subst (up Q u) f) q := by
  first | exact @GlobalTheory.QLog.hasVal_subst | exact GlobalTheory.QLog.hasVal_subst | (intros; apply GlobalTheory.QLog.hasVal_subst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue
section
open IsDedekindDomain IsLocalRing

namespace GlobalTheory.IntAdicHensel

theorem henselianLocalRing_and_finite_residueField :
    ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧
      Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  intro v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers ℚ)
  haveI : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers ℚ)
    (maximalIdeal (v.adicCompletionIntegers ℚ))
  refine ⟨GlobalTheory.henselianLocalRing_of_henselianRing _, ?_⟩
  haveI : Finite (ℤ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv

end GlobalTheory.IntAdicHensel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZeroStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : Sq p, sqPt p t k ∉ L.lattice ∧ (p : ℂ) * sqPt p t k ∈ L.lattice) ∧ sqProd p L t ≠ 0 := by
  first | exact @GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero | exact GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero | (intros; apply GlobalTheory.CMModel.SqNe.sqPt_and_sqProd_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdKernelMultiplierTranslateNegStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_kernel_multiplier_translate_neg : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (φ : ℂ → ℂ), IsKerReps L α S → MulStable L α → (∀ z l, l ∈ L.lattice → φ (z + l) = φ z) → (∀ z s, α * s ∈ L.lattice → φ (z + s) * ∏ t ∈ S, φ (z + s + t) = φ z * ∏ t ∈ S, φ (z + t)) ∧ ∀ z, ∏ t ∈ S, φ (z - t) = ∏ t ∈ S, φ (z + t) := by
  first | exact @GlobalTheory.KerPerm.prod_ker_translate_neg | exact GlobalTheory.KerPerm.prod_ker_translate_neg | (intros; apply GlobalTheory.KerPerm.prod_ker_translate_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRingStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_algebra_topological_ring : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), IsTopologicalRing ℍ[R, a, b] ∧ Continuous (nrm : ℍ[R, a, b] → R) ∧ Continuous (fun x : ℍ[R, a, b] => x.re) ∧ (T2Space R → T2Space ℍ[R, a, b]) := by
  first | exact @GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 | exact GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 | (intros; apply GlobalTheory.quaternion_isTopologicalRing_nrm_re_t2 <;> assumption)
end

