import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0150
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0132
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0143
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0133
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0231
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0023
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import GroundTheory.AutomorphicForms.HermitianBinaryValues
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GreenbergWilesOfPoitouTate
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles.Assembly

theorem arith {a s p1 b h1 lam p2 h2 h0' q0 h0 m arch : ℕ}
    (h4 : a * s * p1 = b * h1 * lam) (h5 : s * p2 = h2 * h0') (h6 : p1 = q0 * p2 * m)
    (h7 : h0 * h2 * m = h1 * arch) (hh1 : 0 < h1) :
    a * h0' * q0 * arch = b * h0 * lam := by
  apply Nat.eq_of_mul_eq_mul_right hh1
  calc a * h0' * q0 * arch * h1 = a * h0' * q0 * (h1 * arch) := by ring
    _ = a * h0' * q0 * (h0 * h2 * m) := by rw [h7]
    _ = h0 * (a * (h2 * h0') * q0 * m) := by ring
    _ = h0 * (a * (s * p2) * q0 * m) := by rw [h5]
    _ = h0 * (a * s * (q0 * p2 * m)) := by ring
    _ = h0 * (a * s * p1) := by rw [h6]
    _ = h0 * (b * h1 * lam) := by rw [h4]
    _ = b * h0 * lam * h1 := by ring

theorem card_pi_submodule {R ι : Type} [Semiring R] [Fintype ι] {X : ι → Type}
    [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)] (L : ∀ i, Submodule R (X i)) :
    Nat.card (Submodule.pi Set.univ L) = ∏ i, Nat.card (L i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
      invFun := fun y => ⟨fun i => (y i).1, fun i _ => (y i).2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem greenbergWiles_of_poitouTate : PoitouTateNormalised → GlobalEulerChar → LocalTateDuality →
    LocalEulerChar → LocalFiniteness → GreenbergWiles := by
  intro hPT hGEC hLTD hLEC hLF
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S ρ hr hl hS hρ μ hμ Av hAv c hc L
  classical
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI hfinD : Finite (TDual (ZMod (l ^ r)) M) := GlobalTheory.CompanionTheory.DualFin.finite_dual_all (ZMod (l ^ r)) M
  obtain ⟨inv, hinv, hnine, hsha⟩ :=
    GlobalTheory.CompanionTheory.GreenbergWiles.poitouTate_instance F Ω l r M S Av μ ρ hρ hμ hPT hl hr hS hAv
  have hρ' : ContAction (twDual μ ρ) := GlobalTheory.T.selmer_group_dual_exact F Ω l r M S Av μ ρ hρ hμ
  have hj : ∀ v, Function.Injective (invAt S Av μ hμ inv v) := fun v =>
    ((hinv _ _ (hAv v)).comp (toMuLoc_bijective S Av μ hμ v)).injective
  have hlf := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r M S Av μ ρ hρ hLF hr hAv
  have hlf' := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r (TDual (ZMod (l ^ r)) M)
    S Av μ (twDual μ ρ) hρ' hLF hr hAv
  haveI : ∀ v : S, Finite (H1 (ρ.comp (locFam S Av v))) := fun v => (hlf v).2.1
  haveI : ∀ v : S, Finite (H2 (ρ.comp (locFam S Av v))) := fun v => (hlf v).2.2
  haveI : ∀ v : S, Finite (H1 ((twDual μ ρ).comp (locFam S Av v))) := fun v => (hlf' v).2.1
  obtain ⟨hH0, hH1, hH2, hH0', hH1'⟩ := GlobalTheory.T.greenberg_wiles_formula F Ω l r M S Av μ ρ hρ
    (invAt S Av μ hμ inv) hμ hfinD hLF hr hAv hnine hsha
  have hloc := GlobalTheory.T.galois_cohomology_localization_exact F Ω l r M S Av μ ρ hρ hμ hLTD hr inv hinv hAv
  have hB := GlobalTheory.CompanionTheory.Pairing.sum_perfect (ZMod (l ^ r)) S (fun v => H1 (ρ.comp (locFam S Av v)))
    (fun v => H1 ((twDual μ ρ).comp (locFam S Av v)))
    (fun v => (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).compr₂
      (invAt S Av μ hμ inv v)) (fun v => (hloc v).1) (fun v => (hloc v).2)
  have hBi : Function.Injective (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ) := by
    unfold sumPair; rw [LinearMap.coe_sum]; exact hB.1
  have hBf : Function.Injective (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ).flip := by
    unfold sumPair; exact hB.2
  have hrange := GlobalTheory.T.tate_shafarevich_duality_h1 F Ω l r M S Av μ ρ hρ (invAt S Av μ hμ inv) hnine
  have count := GlobalTheory.CompanionTheory.Counting.card_comap_mul_card_ker_mul_card_eq (l ^ r) (H1 ρ)
    (H1 (twDual μ ρ)) (∀ v : S, H1 (ρ.comp (locFam S Av v)))
    (∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v)))
    (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ) hBi hBf (loc1 S Av ρ) (loc1 S Av (twDual μ ρ))
    hrange (Submodule.pi Set.univ L)
  have hsel := GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker F Ω l r M S Av μ ρ hρ
  have hsel' := GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker F Ω l r (TDual (ZMod (l ^ r)) M) S Av μ
    (twDual μ ρ) hρ'
  rw [← GlobalTheory.CompanionTheory.Duality.pi_perpCond_eq_annihilator_sumPair F Ω l r M S Av μ ρ hρ _ hj L,
    ← hsel.1 L, ← hsel'.1, ← hsel'.2.1, card_pi_submodule L, hsha.1.2.2.2] at count
  have h5 := GlobalTheory.T.poitou_tate_nine_term_exact F Ω l r M S Av μ ρ hρ (invAt S Av μ hμ inv) hLF hr hAv hnine hH2 hH0'
  have h7 := hGEC F Ω l r M S ρ hr hS hρ c hc
  have hdeg : ∑ v : S, (if ((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal then locDeg v.1 else 0) =
      Module.finrank ℚ F := by
    rw [← GlobalTheory.T.sum_local_degrees_over_l F l (S.filter fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
      (fun v => by rw [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨hS v h, h⟩⟩),
      Finset.sum_filter]
    exact Finset.sum_coe_sort S (fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0)
  have hle := GlobalTheory.CompanionTheory.Gal.localEuler_places F Ω l r M S Av μ ρ hρ hLEC hr hAv
  have h6 : Nat.card (∀ v : S, H1 (ρ.comp (locFam S Av v))) =
      (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) *
        Nat.card (∀ v : S, H2 (ρ.comp (locFam S Av v))) * Nat.card M ^ Module.finrank ℚ F := by
    have hv : ∀ v : S, Nat.card (H1 (ρ.comp (locFam S Av v))) =
        Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v))) *
          Nat.card M ^ (if ((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal then locDeg v.1 else 0) := by
      intro v
      split_ifs with h
      · exact (hle v).1 h
      · rw [pow_zero, mul_one]; exact (hle v).2 h
    rw [Nat.card_pi, Nat.card_pi, Finset.prod_congr rfl (fun v _ => hv v),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  exact arith count h5 h6 h7 Nat.card_pos

end GlobalTheory.CompanionTheory.GreenbergWiles.Assembly
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleNormTrace
section
set_option maxSynthPendingDepth 1

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open GroundTheory.Automorphic GroundTheory.Global
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace

theorem eq_zero_of_not_sqNorm {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {d β : K} (hd0 : d ≠ 0)
    (h : ¬ SqNorm d β) {a b c e : K}
    (hz : (a ^ 2 - d * b ^ 2) - β * (c ^ 2 - d * e ^ 2) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have hd : ∀ r : K, r ^ 2 ≠ d := by
    intro r hr
    have hr0 : r ≠ 0 := by rintro rfl; exact hd0 (by rw [← hr]; ring)
    exact h (sqNorm_of_eq_sq h2 hr.symm hr0 β)
  have hN : ∀ x y : K, x ^ 2 - d * y ^ 2 = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have hy : y = 0 := by
      by_contra hy
      refine hd (x / y) ?_
      field_simp
      linear_combination hxy
    subst hy
    refine ⟨?_, rfl⟩
    have : x ^ 2 = 0 := by linear_combination hxy
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  by_cases hn : c ^ 2 - d * e ^ 2 = 0
  · obtain ⟨rfl, rfl⟩ := hN c e hn
    obtain ⟨rfl, rfl⟩ := hN a b (by linear_combination hz)
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exfalso
    apply h
    have hA : SqNorm d (a ^ 2 - d * b ^ 2) := ⟨a, b, rfl⟩
    have hB : SqNorm d (c ^ 2 - d * e ^ 2) := ⟨c, e, rfl⟩
    have := hA.mul hB.inv
    have he : (a ^ 2 - d * b ^ 2) * (c ^ 2 - d * e ^ 2)⁻¹ = β := by
      field_simp
      linear_combination hz
    rwa [he] at this

theorem aniso_of_not_sqNorm {F : Type} [Field F] [CharZero F] {K : Type} [Field K] [Algebra F K]
    {d β : F} (hd0 : d ≠ 0) (h : ¬ SqNorm (algebraMap F K d) (algebraMap F K β)) :
    ∀ x : Q d β K, qn x = 0 → x = 0 := by
  have h2 : (2 : K) ≠ 0 := by
    have : algebraMap F K 2 ≠ 0 := (map_ne_zero _).2 two_ne_zero
    rwa [map_ofNat] at this
  intro x hx
  obtain ⟨h1, h3, h4, h5⟩ := eq_zero_of_not_sqNorm h2 ((map_ne_zero (algebraMap F K)).2 hd0) h
    (a := x.re) (b := x.imI) (c := x.imJ) (e := x.imK) (by unfold qn at hx; linear_combination hx)
  ext <;> simp [h1, h3, h4, h5]

theorem exists_qn_of_quadraticAlgebra {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {d β t : K}
    (hβ : ¬ SqNorm d β) {x y : QuadraticAlgebra K (-1) t}
    (hxy : x ^ 2 - algebraMap K _ d * y ^ 2 = algebraMap K _ β) :
    ∃ q : Q d β K, qn q = 1 ∧ 2 * q.re = t := by
  have hre := congrArg QuadraticAlgebra.re hxy
  have him := congrArg QuadraticAlgebra.im hxy
  simp only [sq, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_sub,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
    at hre him
  set x0 := x.re
  set x1 := x.im
  set y0 := y.re
  set y1 := y.im
  have hn : x1 ^ 2 - d * y1 ^ 2 ≠ 0 := by
    intro hn
    exact hβ ⟨x0, y0, by linear_combination hre + hn⟩
  set n := x1 ^ 2 - d * y1 ^ 2 with hndef
  refine ⟨⟨-(x0 * x1 - d * y0 * y1) / n, -(y0 * x1 - x0 * y1) / n, x1 / n, -y1 / n⟩, ?_, ?_⟩
  · simp only [qn, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
    rw [hndef]
    linear_combination (x1 ^ 2 - d * y1 ^ 2) * hre
  · simp only
    field_simp
    rw [hndef]
    linear_combination -him

theorem exists_qn_eq_one_two_mul_re {F : Type} [Field F] [NumberField F] (d β t : F)
    (hF : ∀ x : Q d β F, qn x = 0 → x = 0)
    (hl : ∀ u : Pl F, (∀ x : Q d β (Kp u), qn x = 0 → x = 0) →
      ∀ r : Kp u, r ^ 2 ≠ algebraMap F (Kp u) (t ^ 2 - 4)) :
    ∃ x : Q d β F, qn x = 1 ∧ 2 * x.re = t := by
  have key : ∀ a b c e : F, a ^ 2 - d * b ^ 2 - β * c ^ 2 + d * β * e ^ 2 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
    intro a b c e h
    have := hF ⟨a, b, c, e⟩ (by simpa [qn] using h)
    exact ⟨congrArg QuaternionAlgebra.re this, congrArg QuaternionAlgebra.imI this,
      congrArg QuaternionAlgebra.imJ this, congrArg QuaternionAlgebra.imK this⟩
  have hd0 : d ≠ 0 := fun h => one_ne_zero (key 0 1 0 0 (by simp [h])).2.1
  have hβ0 : β ≠ 0 := fun h => one_ne_zero (key 0 0 1 0 (by simp [h])).2.2.1
  have hd : ∀ r : F, r ^ 2 ≠ d := fun r h =>
    one_ne_zero (key r 1 0 0 (by rw [← h]; ring)).2.1
  have hβd : ¬ SqNorm d β := by
    rintro ⟨a, b, h⟩
    exact one_ne_zero (key a b 1 0 (by rw [← h]; ring)).2.2.1
  have ht1 : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ SqNorm (algebraMap F (v.adicCompletion F) d) (algebraMap F _ β) →
      ∀ r : v.adicCompletion F, r ^ 2 ≠ algebraMap F _ (t ^ 2 - 4 * 1) := by
    intro v hv r
    rw [mul_one]
    exact hl (Sum.inr v) (aniso_of_not_sqNorm (K := Kp (Sum.inr v : Pl F)) hd0 hv) r
  have ht2 : ∀ w : InfinitePlace F,
      ¬ SqNorm (algebraMap F w.Completion d) (algebraMap F _ β) →
      ∀ r : w.Completion, r ^ 2 ≠ algebraMap F _ (t ^ 2 - 4 * 1) := by
    intro w hw r
    rw [mul_one]
    exact hl (Sum.inl w) (aniso_of_not_sqNorm (K := Kp (Sum.inl w : Pl F)) hd0 hw) r
  have hbad : (∃ v : HeightOneSpectrum (𝓞 F),
        ¬ SqNorm (algebraMap F (v.adicCompletion F) d) (algebraMap F _ β)) ∨
      ∃ w : InfinitePlace F, ¬ SqNorm (algebraMap F w.Completion d) (algebraMap F _ β) := by
    by_contra H
    push Not at H
    exact hβd ((exists_sq_sub_mul_sq_iff_forall_local hd hβ0).2 ⟨H.1, H.2⟩)
  have hnsq : ∀ r : F, r ^ 2 ≠ t ^ 2 - 4 * 1 := by
    intro r hr
    rcases hbad with ⟨v, hv⟩ | ⟨w, hw⟩
    · exact ht1 v hv (algebraMap F _ r) (by rw [← map_pow, hr])
    · exact ht2 w hw (algebraMap F _ r) (by rw [← map_pow, hr])
  have hL : Fact (∀ r : F, r ^ 2 ≠ -1 + t * r) :=
    ⟨fun r hr => hnsq (2 * r - t) (by linear_combination 4 * hr)⟩
  have hex : ∃ x y : QuadraticAlgebra F (-1) t,
      x ^ 2 - algebraMap F _ d * y ^ 2 = algebraMap F _ β := by
    by_cases hdL : ∃ r : QuadraticAlgebra F (-1) t, r ^ 2 = algebraMap F _ d
    · obtain ⟨r, hr⟩ := hdL
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact (map_ne_zero (algebraMap F (QuadraticAlgebra F (-1) t))).2 hd0 (by rw [← hr]; ring)
      exact sqNorm_of_eq_sq two_ne_zero hr.symm hr0 _
    push Not at hdL
    have hβL : algebraMap F (QuadraticAlgebra F (-1) t) β ≠ 0 := (map_ne_zero _).2 hβ0
    refine (exists_sq_sub_mul_sq_iff_forall_local hdL hβL).2 ⟨fun w => ?_, fun w => ?_⟩
    · refine sqNorm_finite_quadraticAlgebra (γ := 1) hd0 hβ0 w ?_
      exact (Classical.em _).imp_right (ht1 _)
    · refine sqNorm_infinite_quadraticAlgebra (γ := 1) hd0 hβ0 w ?_
      exact (Classical.em _).imp_right (ht2 _)
  obtain ⟨x, y, hxy⟩ := hex
  exact exists_qn_of_quadraticAlgebra two_ne_zero hβd hxy

end GlobalTheory.CompanionTheory.PlaneSA.GlobalTrace
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerKillsSystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Globalize

lemma exists_pow_smul_uniform {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (P : Submodule R M) (hP : P.FG) (N : ℕ → Submodule R M) (f : R)
    (h : ∀ x ∈ P, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n) :
    ∃ k : ℕ, ∀ n, ∀ x ∈ P, f ^ k • x ∈ N n := by
  classical
  obtain ⟨s, rfl⟩ := hP
  have h' : ∀ x ∈ s, ∃ k : ℕ, ∀ n, f ^ k • x ∈ N n :=
    fun x hx => h x (Submodule.subset_span (Finset.mem_coe.2 hx))
  choose! k hk using h'
  refine ⟨s.sup k, fun n x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ s := Finset.mem_coe.1 hy
    have e : f ^ s.sup k • y = f ^ (s.sup k - k y) • f ^ k y • y := by
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hy')]
    rw [e]
    exact (N n).smul_mem _ (hk y hy' n)
  | zero => rw [smul_zero]; exact (N n).zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact (N n).add_mem hy hz
  | smul r y _ hy => rw [smul_comm]; exact (N n).smul_mem _ hy

variable {X : Scheme.{0}}

def killIdeal {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (V : X.Opens) :
    Ideal Γ(X, V) :=
  ⨅ n, (secsSub (S n) V).colon (secs D V)

lemma mem_killIdeal {E : X.Modules} {D : Subobject E} {S : ℕ → Subobject E} {V : X.Opens}
    {a : Γ(X, V)} : a ∈ killIdeal D S V ↔ ∀ n, ∀ x ∈ secs D V, a • x ∈ secs (S n) V := by
  simp only [killIdeal, Submodule.mem_iInf, Submodule.mem_colon]
  rfl

theorem exists_pow_le_killIdeal [IsLocallyNoetherian X] {E : X.Modules} (hE : IsCoherent E)
    (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) (S : ℕ → Subobject E)
    (J₀ : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ f ∈ J₀.ideal V, ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) :
    ∃ m : ℕ, J₀.ideal V ^ m ≤ killIdeal D S V := by
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  have hfin : Module.Finite Γ(X, V) Γ((D : X.Modules), V) :=
    (isCoherent_subobject hE D hD).2 V V.2
  let φ : Γ((D : X.Modules), V) →ₗ[Γ(X, V)] Γ(E, V) :=
    { toFun := D.arrow.app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hr : secsSub D V = LinearMap.range φ := Submodule.ext fun _ => Iff.rfl
  have hP : (secsSub D V).FG := by
    rw [hr, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map φ
  have hrad : J₀.ideal V ≤ (killIdeal D S V).radical := by
    intro f hf
    obtain ⟨k, hk⟩ := exists_pow_smul_uniform (secsSub D V) hP (fun n => secsSub (S n) V) f
      (fun x hx => h f hf x hx)
    exact ⟨k, mem_killIdeal.2 fun n x hx => hk n x hx⟩
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

end GlobalTheory.CompanionTheory.GE.Globalize

namespace GlobalTheory.CompanionTheory.GE.Globalize

variable {X : Scheme.{0}}

theorem pow_le_killIdeal_basicOpen {E : X.Modules} (D : Subobject E)
    [(D : X.Modules).IsQuasicoherent] (S : ℕ → Subobject E) (J₀ : X.IdealSheafData)
    (V : X.affineOpens) (m : ℕ) (hV : J₀.ideal V ^ m ≤ killIdeal D S V) (g : Γ(X, V)) :
    J₀.ideal (X.affineBasicOpen g) ^ m ≤ killIdeal D S (X.basicOpen g) := by
  have hmap : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) =
      J₀.ideal (X.affineBasicOpen g) ^ m := by
    rw [Ideal.map_pow, J₀.map_ideal_basicOpen]
    rfl
  intro a ha
  rw [← hmap] at ha
  refine (Ideal.map_le_iff_le_comap.2 ?_ : Ideal.map (resO (X.basicOpen_le g)) (J₀.ideal V ^ m) ≤
    killIdeal D S (X.basicOpen g)) ha
  intro r hr
  rw [Ideal.mem_comap]
  refine mem_killIdeal.2 fun n x hx => ?_
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨e, y', hy'⟩ := qcoh_exists_res_eq (D : X.Modules) V.2 g y
  obtain ⟨z, hz⟩ := mem_killIdeal.1 (hV hr) n _ ⟨y', rfl⟩
  have key : resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y) ∈
      secs (S n) (X.basicOpen g) := by
    refine ⟨resF _ (X.basicOpen_le g) z, ?_⟩
    rw [← resF_app, hz, resF_smul, resF_app, hy', Scheme.Modules.Hom.app_smul, smul_comm]
  obtain ⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le g) g) := X.toRingedSpace.isUnit_res_basicOpen g
  have e2 : resO (X.basicOpen_le g) r • D.arrow.app _ y =
      ((u⁻¹ : (Γ(X, X.basicOpen g))ˣ) : Γ(X, X.basicOpen g)) ^ e •
        (resO (X.basicOpen_le g) g ^ e • (resO (X.basicOpen_le g) r • D.arrow.app _ y)) := by
    rw [smul_smul, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_smul]
  rw [e2]
  exact (secsSub (S n) (X.basicOpen g)).smul_mem _ key

theorem mem_secs_of_local {E : X.Modules} [E.IsQuasicoherent] (T : Subobject E)
    [(T : X.Modules).IsQuasicoherent] (U : X.affineOpens) (x : Γ(E, U))
    (h : ∀ p ∈ (U : X.Opens), ∃ W : X.affineOpens, p ∈ (W : X.Opens) ∧
      ∃ hW : (W : X.Opens) ≤ U, resF E hW x ∈ secs T W) :
    x ∈ secs T U := by
  choose W hpW hWU hW using h
  have h0 : (cokernel.π T.arrow).app U x = 0 := by
    refine eq_of_forall_resF (cokernel T.arrow) (fun p : (U : X.Opens) => (W p.1 p.2 : X.Opens))
      (fun p => hWU p.1 p.2) ?_ _ 0 ?_
    · intro p hp
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW p hp⟩
    · intro p
      obtain ⟨z, hz⟩ := hW p.1 p.2
      rw [resF_app, ← hz, map_zero, (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow (W p.1 p.2).2).apply_apply_eq_zero z]
  exact (GlobalTheory.QCoh.exact_cokernel_π_app T.arrow U.2 x).1 h0

end GlobalTheory.CompanionTheory.GE.Globalize

namespace GlobalTheory.CompanionTheory.GE.Globalize

theorem exists_uniform_pow_kills : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] [CompactSpace X]
    {E : X.Modules}, IsCoherent E → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent →
    ∀ (S : ℕ → Subobject E), (∀ n, (S n : X.Modules).IsQuasicoherent) →
    ∀ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V →
      ∀ x ∈ secs D V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V) →
    ∃ m : ℕ, ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ (powIdeal J₀ m).ideal U →
      ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro X _ _ E hE D hD S hS J₀ hJ
  choose mV hmV using fun V : X.affineOpens => exists_pow_le_killIdeal hE D hD S J₀ V (hJ V)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => ((V : X.Opens) : Set X))
    (fun V => (V : X.Opens).isOpen) (by
      intro p _
      obtain ⟨V, hV⟩ : ∃ V : X.affineOpens, p ∈ (V : X.Opens) := by
        obtain ⟨V, hV, hpV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
          (show p ∈ (⊤ : X.Opens) from trivial)
        exact ⟨⟨V, hV⟩, hpV⟩
      exact Set.mem_iUnion.2 ⟨V, hV⟩)
  refine ⟨t.sup mV, fun n U a ha x hx => ?_⟩
  haveI : E.IsQuasicoherent := hE.1
  haveI : (D : X.Modules).IsQuasicoherent := hD
  haveI := hS n
  refine mem_secs_of_local (S n) U (a • x) fun p hpU => ?_
  obtain ⟨V, hVt, hpV⟩ : ∃ V ∈ t, p ∈ ((V : X.Opens) : Set X) := by
    simpa using ht (Set.mem_univ p)
  obtain ⟨f, g, hfg, hpf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 p ⟨hpU, hpV⟩
  have hWU : X.basicOpen g ≤ (U : X.Opens) := hfg ▸ X.basicOpen_le f
  refine ⟨X.affineBasicOpen g, (show p ∈ X.basicOpen g from hfg ▸ hpf), hWU, ?_⟩
  have hVm : J₀.ideal V ^ t.sup mV ≤ killIdeal D S V :=
    (Ideal.pow_le_pow_right (Finset.le_sup hVt)).trans (hmV V)
  have hk := pow_le_killIdeal_basicOpen D S J₀ V _ hVm g
  have hWU' : X.affineBasicOpen g ≤ U := hWU
  have ha' : resO hWU a ∈ J₀.ideal (X.affineBasicOpen g) ^ t.sup mV := by
    have := Ideal.mem_map_of_mem (resO hWU) (show a ∈ J₀.ideal U ^ t.sup mV from ha)
    rw [Ideal.map_pow] at this
    exact (J₀.map_ideal hWU') ▸ this
  obtain ⟨y, rfl⟩ := hx
  have e3 := resF_smul E hWU a (D.arrow.app U y)
  erw [e3, resF_app]
  exact mem_killIdeal.1 (hk ha') n _ ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.GE.Globalize
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateEndomorphismSeriesExists
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.LTPer

theorem map_subst_comm {A B : Type} [CommRing A] [CommRing B] (h : A →+* B) {F G : PowerSeries A}
    {F' : PowerSeries B} (hF' : PowerSeries.map h F = F')
    (hF : PowerSeries.constantCoeff F = 0) (hG : PowerSeries.constantCoeff G = 0)
    (hs : PowerSeries.subst G F = PowerSeries.subst F G) :
    PowerSeries.subst (PowerSeries.map h G) F' = PowerSeries.subst F' (PowerSeries.map h G) := by
  subst hF'
  have h2 := congrArg (MvPowerSeries.map h) hs
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF)] at h2
  exact h2

open GlobalTheory.CompanionTheory.LTHodge.CharEx GroundTheory.LocalField GroundTheory.LocalField.FormalGroup ValuativeRel in

theorem exists_series_comm : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ a : ↥(OL K),
    ∃ φ : PowerSeries ↥(OL K), PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      PowerSeries.subst φ (ltSeries π) = PowerSeries.subst (ltSeries π) φ := by
  intro l _ K π hπ a
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let e : ↥(OL K) ≃+* 𝒪[↥K.1] := intEquiv K
  let es : 𝒪[↥K.1] →+* ↥(OL K) := (e.symm : 𝒪[↥K.1] →+* ↥(OL K))
  have hp : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hf := isLubinTateSeries_ltPoly (e π)
  have hm := map_ltSeries K hp
  have hes : (intEquiv K).symm (e π) = π := e.symm_apply_apply π
  rw [hes] at hm
  have hF : PowerSeries.map es (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = ltSeries π := by
    rw [← hm]
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map]
    exact e.symm_apply_apply _
  have hF0 : PowerSeries.constantCoeff (ltPoly (e π) : PowerSeries 𝒪[↥K.1]) = 0 :=
    hf.constantCoeff_eq_zero
  let h := lubinTateHom hp hf hf (e a)
  have h0 : PowerSeries.constantCoeff h.toPowerSeries = 0 := h.constantCoeff_eq_zero
  have h1 : PowerSeries.coeff 1 h.toPowerSeries = e a := coeff_one_lubinTateHom hp hf hf (e a)
  have hs := subst_lubinTateHom hp hf hf (e a)
  refine ⟨PowerSeries.map es h.toPowerSeries, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rw [PowerSeries.coeff_map, h1]
    exact e.symm_apply_apply a
  · exact map_subst_comm es hF hF0 h0 hs

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateScaledIterateTendsStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_scaled_iterate_tends : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      ∃ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.LogConv.log_converges | exact GlobalTheory.CompanionTheory.LTPer.LogConv.log_converges | (intros; apply GlobalTheory.CompanionTheory.LTPer.LogConv.log_converges <;> assumption)
end
end

