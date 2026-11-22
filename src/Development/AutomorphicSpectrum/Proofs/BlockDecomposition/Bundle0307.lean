import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0284
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompShiftZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DescOfDes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0299
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpEpsilonRootIdempotentSum
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Frob

variable {l : ℕ} {R : Type} [CommRing R] (φ : R →+* R)

theorem mem_span_of_frob_mem (hb : Function.Bijective φ) {y p : R}
    (h : φ y ∈ Ideal.span {φ p}) : y ∈ Ideal.span {p} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨c', rfl⟩ := hb.2 c
  exact Ideal.mem_span_singleton'.2 ⟨c', hb.1 (by rw [map_mul, hc])⟩

theorem mem_span_of_pow_mem (hφ : ∀ x, φ x = x ^ l) (hb : Function.Bijective φ) {x p : R}
    (N : ℕ) (h : x ^ l ^ N ∈ Ideal.span {p ^ l ^ N}) : x ∈ Ideal.span {p} := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih (mem_span_of_frob_mem φ hb ?_)
    rw [hφ, hφ, ← pow_mul, ← pow_mul, ← pow_succ]
    exact h

theorem sub_pow_of_frob (hφ : ∀ x, φ x = x ^ l) (a b : R) (N : ℕ) :
    (a - b) ^ l ^ N = a ^ l ^ N - b ^ l ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih, ← hφ, map_sub, hφ, hφ]

end Frob

theorem root_pow {l : ℕ} {T : Type} [Monoid T] {x : ℕ → T} (hx : ∀ m, x (m + 1) ^ l = x m) (m k : ℕ) :
    x (m + k) ^ l ^ k = x m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' l k, pow_mul, ← add_assoc, hx, ih]

variable {l : ℕ} [Fact l.Prime]

def powSum (A : PAlg l) (u : (A.cont ℤ_[l]).A) (N : ℕ) : (A.cont ℤ_[l]).A :=
  ∑ c : ZMod (l ^ N), ind A N c * u ^ c.val

theorem ev_powSum (A : PAlg l) (u : (A.cont ℤ_[l]).A) (N : ℕ) (z : ℤ_[l]) :
    Hom.f (A.evCont z) (powSum A u N) = Hom.f (A.evCont z) u ^ (PadicInt.toZModPow N z).val := by
  rw [powSum, map_sum]
  simp only [map_mul, map_pow, ev_ind, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem sub_powSum_mem (A : PAlg l) {u ρ : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (hρ : ∀ n, ρ (n + 1) ^ l = ρ n)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) (ρ 0) -
      Hom.f (A.evCont z) (u 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {A.pi ^ (l ^ m)})
    (N : ℕ) : ρ N - powSum A (u N) N ∈ Ideal.span {(A.cont ℤ_[l]).pi} := by
  have hf : ∀ x : (A.cont ℤ_[l]).A, (A.cont ℤ_[l]).frob x = x ^ l := fun _ => rfl
  refine mem_span_of_pow_mem (l := l) (A.cont ℤ_[l]).frob hf (A.cont ℤ_[l]).frob_bijective N ?_
  have h1 : ρ N ^ l ^ N = ρ 0 := by simpa using root_pow hρ 0 N
  have h2 : u N ^ l ^ N = u 0 := by simpa using root_pow hu 0 N
  rw [sub_pow_of_frob (l := l) _ hf, h1, mem_span_pi_pow]
  intro z
  rw [map_sub, map_pow, ev_powSum, ← pow_mul, mul_comm, pow_mul, ← map_pow, h2]
  exact h0 N z

theorem sharp_powSum (A : PAlg l) {u : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (m k : ℕ) (hv : (A.cont ℤ_[l]).sharp (u m) ^ l ^ m = 1) :
    (A.cont ℤ_[l]).sharp (powSum A (u (m + k)) (m + k) ^ l ^ k) =
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val := by
  set B := powSum A (u (m + k)) (m + k) ^ l ^ k with hB
  set v := (A.cont ℤ_[l]).sharp (u m) with hvdef
  set T := ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * v ^ c.val with hT
  have hle : m ≤ m + k := Nat.le_add_right m k
  have h1 : ∀ c' : ZMod (l ^ (m + k)), ind A (m + k) c' * B = ind A (m + k) c' * u m ^ c'.val := by
    intro c'
    refine cont_ext fun z => ?_
    rw [map_mul, map_mul, ev_ind]
    split_ifs with h
    · have hr : Hom.f (A.evCont z) (u (m + k)) ^ l ^ k = Hom.f (A.evCont z) (u m) := by
        rw [← map_pow, root_pow hu]
      rw [hB, map_pow, ev_powSum, map_pow, h, ← pow_mul, mul_comm c'.val, pow_mul, hr]
    · simp
  have h2 : ∀ (c' : ZMod (l ^ (m + k))) (c : ZMod (l ^ m)), ZMod.cast c' ≠ c →
      ind A (m + k) c' * ind A m c = 0 := by
    intro c' c hc
    refine cont_ext fun z => ?_
    rw [map_mul, ev_ind, ev_ind, map_zero]
    split_ifs with h h'
    · exact absurd (by rw [← h', ← h, PadicInt.cast_toZModPow m (m + k) hle]) hc
    all_goals simp
  have h3 : ∀ c' : ZMod (l ^ (m + k)),
      ind A (m + k) c' * ind A m (ZMod.cast c') = ind A (m + k) c' := by
    intro c'
    refine cont_ext fun z => ?_
    rw [map_mul, ev_ind, ev_ind]
    split_ifs with h h'
    · simp
    · exact absurd (by rw [← h, PadicInt.cast_toZModPow m (m + k) hle]) h'
    all_goals simp
  have h4 : ∀ c' : ZMod (l ^ (m + k)), v ^ (ZMod.cast c' : ZMod (l ^ m)).val = v ^ c'.val := by
    intro c'
    rw [pow_eq_pow_mod c'.val hv, ← ZMod.natCast_val, ZMod.val_natCast]
  have key : ∀ c' : ZMod (l ^ (m + k)), (A.cont ℤ_[l]).sharp (ind A (m + k) c') * (A.cont ℤ_[l]).sharp B =
      (A.cont ℤ_[l]).sharp (ind A (m + k) c') * T := by
    intro c'
    rw [← map_mul, h1, map_mul, map_pow, hT, Finset.mul_sum, Finset.sum_eq_single (ZMod.cast c')]
    · rw [← mul_assoc, ← map_mul, h3, h4]
    · intro c _ hc
      rw [← mul_assoc, ← map_mul, h2 c' c (Ne.symm hc), sharp_zero, zero_mul]
    · simp
  have hsum := sum_sharp_eq_one (A.cont ℤ_[l]) (coi_ind A (m + k))
  calc (A.cont ℤ_[l]).sharp B = (∑ c', (A.cont ℤ_[l]).sharp (ind A (m + k) c')) * (A.cont ℤ_[l]).sharp B := by
        rw [hsum, one_mul]
    _ = (∑ c', (A.cont ℤ_[l]).sharp (ind A (m + k) c')) * T := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c' _ => key c'
    _ = T := by rw [hsum, one_mul]

theorem sharp_roots_core (A : PAlg l) {u ρ : ℕ → (A.cont ℤ_[l]).A} (hu : ∀ n, u (n + 1) ^ l = u n)
    (hs : (A.cont ℤ_[l]).sharp (u 0) = 1) (hρ : ∀ n, ρ (n + 1) ^ l = ρ n)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f (A.evCont z) (ρ 0) -
      Hom.f (A.evCont z) (u 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {A.pi ^ (l ^ m)})
    (m : ℕ) : (A.cont ℤ_[l]).sharp (ρ m) =
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val := by
  have hv : (A.cont ℤ_[l]).sharp (u m) ^ l ^ m = 1 := by
    rw [← map_pow, (by simpa using root_pow hu 0 m : u m ^ l ^ m = u 0), hs]
  have hk : ∀ k, (A.cont ℤ_[l]).sharp (ρ m) -
      ∑ c : ZMod (l ^ m), (A.cont ℤ_[l]).sharp (ind A m c) * (A.cont ℤ_[l]).sharp (u m) ^ c.val ∈
      Ideal.span {(l : (A.cont ℤ_[l]).U) ^ (k + 1)} := by
    intro k
    have h := (RL.sharp_cong (A.cont ℤ_[l])).1 _ _ k (sub_powSum_mem A hu hρ h0 (m + k))
    rwa [root_pow hρ, sharp_powSum A hu m k hv] at h
  refine sub_eq_zero.1 (IsHausdorff.haus
    (inferInstance : IsHausdorff (Ideal.span {(l : (A.cont ℤ_[l]).U)}) (A.cont ℤ_[l]).U) _ fun k => ?_)
  refine smodEq_iff.2 ?_
  rw [sub_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hk k)
  exact Ideal.mem_span_singleton'.2 ⟨c * l, by rw [← hc, pow_succ]; ring⟩

theorem sharp_roots_universal {l : ℕ} [Fact l.Prime] (ε : Eps l) (ρ : ℕ → ((base l).cont ℤ_[l]).A)
    (h0 : ∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) (ρ 0) -
      (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)})
    (hρ : ∀ m, ρ (m + 1) ^ l = ρ m) (m : ℕ) : ((base l).cont ℤ_[l]).sharp (ρ m) =
    ∑ c : ZMod (l ^ m), ((base l).cont ℤ_[l]).sharp (GlobalTheory.CompanionTheory.ContUniv.ind (base l) m c) *
      ((base l).cont ℤ_[l]).sharp (((base l).cont ℤ_[l]).s (ε.e m)) ^ c.val := by
  have hev : ∀ (n : ℕ) (z : ℤ_[l]),
      Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e n)) = (base l).s (ε.e n) :=
    fun n z => RingHom.congr_fun (Hom.comm ((base l).evCont z)) _
  refine sharp_roots_core (base l) (u := fun n => ((base l).cont ℤ_[l]).s (ε.e n)) (fun n => ?_)
    (ε.sharp_e _) hρ (fun k z => ?_) m
  · show ((base l).cont ℤ_[l]).s (ε.e (n + 1)) ^ l = ((base l).cont ℤ_[l]).s (ε.e n)
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]
  · show Hom.f ((base l).evCont z) (ρ 0) -
      Hom.f ((base l).evCont z) (((base l).cont ℤ_[l]).s (ε.e 0)) ^ _ ∈ _
    rw [hev]
    exact h0 k z

end GlobalTheory.CompanionTheory.ContUniv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepDesc
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.DescTest

section
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem step_desc (hOut : D.Out l) (hk : k = false ∨ ρ = 0) (r : ℕ) :
    Desc (ε.qk 1 - 1) (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).fn (jE (F.pt κ)) :=
  desc_fil F κ ε k n ρ hρ hk r _ (des_qk hOut ε (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).1 n (ρ r))

theorem xi_thick (T : (F.pt κ).Elements) :
    ((gE F κ k n).obj T).i ((base l).cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i)) ∈ ((gE F κ k n).obj T).J :=
  xi_mem F κ k n T _ ((GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.1 T.1 n)

theorem mu_factor : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i :=
  (GlobalTheory.CompanionTheory.EpsFacts.eps_facts ε).2.2.2.1

end

set_option maxHeartbeats 1000000 in

theorem main : ∀ {l : ℕ} [Fact l.Prime], D.Out l → ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), (k = false ∨ ρ = 0) →
    Desc (Polynomial.X : Polynomial ℤ) (gE F κ k n ⋙ (flt F κ ε k n ρ hρ).rees) (jE (F.pt κ)) := by
  intro l _ hOut O _ F κ ε k n ρ hρ hk
  exact desc_flt (b := bs l k n) (L := Lc F κ k n) (Λ := Acris l) (F.pt κ) ((base l).cris n) (gE F κ k n) ρ hρ
    ε.μ (ε.μ_mem k (base l) n) (jE (F.pt κ)) (ε.qk 1 - 1) (∑ i ∈ Finset.range l, ε.qk 1 ^ i)
    (mu_factor ε) (xi_thick F κ ε k n) (step_desc F κ ε k n ρ hρ hOut hk)

end GlobalTheory.CompanionTheory.DescTest
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatibleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_cech_cover_compatible : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a b c : ℤ) (h : a + b = c) (e : ℕ) (S : Finset ι) (x : SecOn (pw (N (e + 1)) a) (D (e + 1) S)) (y : SecOn (pw (N (e + 1)) b) (D (e + 1) S)), red I Y N D β hβ v hN hDβ c e S (SecOnR.of _ _ _ (secMulOn h x y)) = SecOnR.of _ _ _ (secMulOn h ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ x))) ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ b e S (SecOnR.of _ _ _ y)))) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.red_secMulOn | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.red_secMulOn | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.red_secMulOn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_cech_restriction_commutes : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a : ℤ) (h : a = 0) (e : ℕ) (S : Finset ι), red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ (oneOn (N (e + 1)) h (D (e + 1) S))) = SecOnR.of _ _ _ (oneOn (N e) h (D e S)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.red_oneOn | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.red_oneOn | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.red_oneOn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpensStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_restriction_compatible_opens : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V W : (Y (e + 1)).left.Opens) (V' W' : (Y e).left.Opens) (hV : V' ≤ β e ⁻¹ᵁ V) (hW : W' ≤ β e ⁻¹ᵁ W) (h : W ≤ V) (h' : W' ≤ V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V), redL I Y β hβ L w hL e W W' hW (SecOnR.restrict _ _ h x) = SecOnR.restrict _ _ h' (redL I Y β hβ L w hL e V V' hV x) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousFormStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_section_homogeneous_form : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  first | exact @GlobalTheory.CompanionTheory.GE.ker_thickι_chart | exact GlobalTheory.CompanionTheory.GE.ker_thickι_chart | (intros; apply GlobalTheory.CompanionTheory.GE.ker_thickι_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransitionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_twisted_section_transition : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) (y : SecOn (pw (N e) (-d)) (D e S)), secMulOn rfl σ y = oneOn (N e) (add_neg_cancel d) (D e S) → Function.Bijective (mulT I Y N D d e t S σ) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVeryAmpleOpensExistStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_very_ample_opens_exist : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : LB (Y 0).left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy (Y 0).hom H s → ∃ D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens, (∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) ∧ (∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) ∧ (∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) ∧ (∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) ∧ (∀ e, ⨆ i, D e {i} = ⊤) ∧ (∀ e S, S.Nonempty → IsAffineOpen (D e S)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_basicOpens_of_tower | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_basicOpens_of_tower | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_basicOpens_of_tower <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentation
section
noncomputable section

open Finset Matrix

namespace GlobalTheory.CompanionTheory.RgTorus

open PositivityTheory.RgDs.K

variable {n : ℕ}

theorem tor_inv (θ : Fin n → ℝ) :
    (tor θ)⁻¹ = Matrix.diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
  apply Matrix.inv_eq_left_inv
  simp only [tor, Matrix.diagonal_mul_diagonal, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  exact Matrix.diagonal_one

theorem adC_tor_ne (θ : Fin n → ℝ) {p q : Fin n × Fin n} (h : p ≠ q) : adC (tor θ) p q = 0 := by
  unfold adC
  rw [tor_inv]
  by_cases h1 : q.1 = p.1
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1.symm h2)
    rw [Matrix.diagonal_apply_ne _ h2, mul_zero]
  · unfold tor
    rw [Matrix.diagonal_apply_ne _ h1, zero_mul]

theorem adC_tor_self (θ : Fin n → ℝ) (p : Fin n × Fin n) :
    adC (tor θ) p p = Complex.exp (((θ p.1 - θ p.2 : ℝ) : ℂ) * Complex.I) := by
  unfold adC
  rw [tor_inv]
  unfold tor
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rhoTorus : RhoTorus := by
  intro n ε Λ T m θ k hk a x
  unfold rhoA
  rw [hk, Finset.sum_eq_single x.2]
  · congr 1
    simp only [adC_tor_self]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  · intro w _ hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (adC_tor_ne θ hi), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CompanionTheory.RgTorus
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusWeightDecomposition
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.RgDsTor

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW PositivityTheory.RgDs.K

variable {n : ℕ}

theorem diagI_inK (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inK ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  unfold inK inG Jm
  refine ⟨?_, ?_⟩
  · rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add, ← Matrix.diagonal_zero]
    congr 1
    funext a
    simp only [Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem tor_eq_exp (θ : Fin n → ℝ) :
    tor θ = NormedSpace.exp (((1 : ℝ) : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  rw [Complex.ofReal_one, one_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [Complex.exp_eq_exp_ℂ]

private theorem pow_apply_eq_pow_smul_of_apply_eq_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) (k : ℕ) : (A ^ k) w = c ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ']

theorem exp_apply_of_eigen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (A : V →L[ℂ] V) (c : ℂ) (w : V) (h : A w = c • w) :
    NormedSpace.exp A w = Complex.exp c • w := by
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL (ContinuousLinearMap.apply ℂ V w)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const w
  rw [← Complex.exp_eq_exp_ℂ] at h2
  have h3 : HasSum (fun k : ℕ => (ContinuousLinearMap.apply ℂ V w) (((k.factorial : ℂ))⁻¹ • A ^ k))
      (Complex.exp c • w) := by
    convert h2 using 1
    funext k
    rw [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      pow_apply_eq_pow_smul_of_apply_eq_smul A c w h k, smul_smul, smul_eq_mul]
  have e := h1.unique h3
  rwa [ContinuousLinearMap.apply_apply] at e

private theorem diagonal_mul_I_eq_sum_single (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) =
      ∑ a, ((θ a : ℂ) * Complex.I) • Matrix.single a a (1 : ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hij rfl

theorem dtau_diag_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (θ : Fin n → ℝ) :
    T.dτ (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) T.w =
      (((∑ a, Λ a * θ a : ℝ) : ℂ) * Complex.I) • T.w := by
  rw [diagonal_mul_I_eq_sum_single, map_sum, ContinuousLinearMap.sum_apply]
  simp_rw [map_smul, ContinuousLinearMap.smul_apply, T.13, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem torW : TorW := by
  intro n ε Λ T θ k hk
  have hX := diagI_inK ε θ
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ 1, hk, tor_eq_exp])
  rw [← h1, KType.op_curve T hX γ hγ 1]
  apply exp_apply_of_eigen
  rw [ContinuousLinearMap.smul_apply, dtau_diag_w, smul_smul, Complex.ofReal_one, one_mul]

end GlobalTheory.CompanionTheory.RgDsTor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharactersDeRhamJumpZeroStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_induced_agree : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ),
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) → (∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1) →
      ∀ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) →
      (∀ σ : ↥(Dec (F := E) A), (σ : G E Ω) ∈ V → (σ : G E Ω) ∈ Ine (F := E) A → ψ σ = 1) →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ 0 := by
  first | exact @GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | exact GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia | (intros; apply GlobalTheory.CompanionTheory.PotUnr.isdRJ_zero_of_trivial_on_open_inertia <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphism
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrisDP

theorem wn_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ),
    IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  intro l _ K r n
  let F₀ : WittVector l r.k →+* (base l).Acr0 :=
    (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))
  refine RL.pd_mor (Ideal.Quotient.mk _) ((base l).mkAcr n) (Ideal.span {(l : WittVector l r.k)}) (base l).PFil0
    (Wc.pd l r.k n) (B.DD true (base l) n) F₀ (Mid.wn r n) Ideal.Quotient.mk_surjective
    (pdI_l l (witt_unit l r.k)) (Wc.isPd l r.k n) ((base l).isPd_pdPFil n) ?_ ?_
  · intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  · intro a
    rw [Mid.wn_mk]
    exact (base l).cris_algebraMap n (WittVector.map r.s a)

end GlobalTheory.CompanionTheory.CrisDP
end
end

