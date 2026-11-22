import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT.KerBy

theorem ev_nsmul {La Q : Type} [AddCommGroup La] [Group Q] (f : La → Q) (hadd : ∀ x y, f (x + y) = f x * f y)
    (e : ℕ) (y : La) : f (e • y) = f y ^ e := by
  induction e with
  | zero =>
    have h := hadd 0 0
    rw [add_zero] at h
    simpa using (mul_eq_left.1 h.symm)
  | succ e ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem pow_eq_one_at_geom (hC : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (e : ℕ) (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f)
    (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (g : Over.mk x₀ ⟶ o.A)
    (hg : ∃ t : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, t.IsGen) :
    g ^ e = 1 := by
  have hpr : p.Prime := Fact.out
  obtain ⟨e', he', hk⟩ := o.kerP
  have hn : g ^ e' = 1 := hk _ g hg
  have hpos : 0 < e' := by
    rcases Nat.eq_zero_or_pos e' with h | h
    · subst h
      have := (Nat.coprime_zero_left p).1 he'
      exact absurd this hpr.one_lt.ne'
    · exact h
  let φ := Spec.preimage (x₀ ≫ t)
  have hβ : x₀ ≫ t = spMap φ.hom := by
    simp [spMap, φ]
  obtain ⟨I, -⟩ := o.geom k x₀ φ.hom hβ
  have hunit : ∀ m : ℕ, m.Coprime p → ((m : ℕ) : k) ≠ 0 := fun m hm => by
    have := (b.unit m hm).map φ.hom
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨y, hy⟩ := (I.onto e' hpos he' g).1 hn
  have hadd : ∀ m, ∀ u v, I.ev m (u + v) = I.ev m u * I.ev m v := fun m u v => I.add m u v

  have vanish : ∀ (m : ℕ), 0 < m → m.Coprime p → ∀ y' z : D.La, I.ev m y' ^ 2 = g →
      I.ζ m ^ (2 * D.EF y' z) = 1 := by
    intro m hm hmp y' z ha
    have ha1 : I.ev m y' ^ m = 1 := (I.onto m hm hmp _).2 ⟨y', rfl⟩
    have hb1 : I.ev m z ^ m = 1 := (I.onto m hm hmp _).2 ⟨z, rfl⟩
    have hgen : ∃ t : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ I.ev m y' ^ 2) (fst o.A (Over.mk x₀))).left).Gen,
        t.IsGen := ha ▸ hg
    have hc := hC S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ m (hunit m hmp) _ _ ha1 hb1 hgen _
      (I.isom m hm hmp y' z)
    exact ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (hc.trans (map_one _).symm)
  have key : ∀ z, (e' : ℤ) ∣ D.EF y z := by
    intro z
    by_cases hp2 : p = 2
    · subst hp2
      have hodd : Odd e' := Nat.odd_iff.2 (by
        rcases Nat.even_or_odd e' with h | h
        · exact absurd (Nat.Coprime.coprime_dvd_left (even_iff_two_dvd.1 h) he') (by norm_num)
        · exact Nat.odd_iff.1 h)
      obtain ⟨r, hr⟩ := hodd
      have h2 : 2 • ((r + 1) • y) = y + e' • y := by
        rw [smul_smul, hr]
        rw [show (2 * (r + 1)) = 1 + (2 * r + 1) by ring, add_smul, one_smul]
      have ha : I.ev e' ((r + 1) • y) ^ 2 = g := by
        rw [← ev_nsmul _ (hadd e'), h2, hadd, ev_nsmul _ (hadd e'), hy, hn, _root_.mul_one]
      have h1 := vanish e' hpos he' _ z ha
      have h3 := ((I.ζ_prim e' hpos he').zpow_eq_one_iff_dvd _).1 h1
      rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h4 : (e' : ℤ) ∣ (((r + 1) * 2 : ℕ) : ℤ) * D.EF y z := by
        have : (2 : ℤ) * (((r + 1 : ℕ) : ℤ) * D.EF y z) = (((r + 1) * 2 : ℕ) : ℤ) * D.EF y z := by push_cast; ring
        rw [← this]; exact_mod_cast h3
      have hcop : IsCoprime (e' : ℤ) (((r + 1) * 2 : ℕ) : ℤ) := by
        rw [Nat.isCoprime_iff_coprime]
        have : (r + 1) * 2 = e' + 1 := by omega
        rw [this]
        exact (Nat.coprime_self_add_right.2 (Nat.coprime_one_right e'))
      exact hcop.dvd_of_dvd_mul_left h4
    · have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hpr).2 (Ne.symm hp2)
      have hmp : (e' * 2).Coprime p := Nat.Coprime.mul he' h2p
      have ha : I.ev (e' * 2) y ^ 2 = g := by
        rw [I.tower e' 2 hpos two_pos hmp y, hy]
      have h1 := vanish (e' * 2) (by omega) hmp y z ha
      have h3 := ((I.ζ_prim (e' * 2) (by omega) hmp).zpow_eq_one_iff_dvd _).1 h1
      have h4 : (e' : ℤ) * 2 ∣ D.EF y z * 2 := by
        have : (2 : ℤ) * D.EF y z = D.EF y z * 2 := by ring
        rw [← this]; exact_mod_cast h3
      exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / e'
      map_add' := fun u v => by
        rw [map_add, Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (e' : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = e' • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev e' y ^ e := by rw [hy]
    _ = I.ev e' (e • y) := (ev_nsmul _ (hadd e') e y).symm
    _ = 1 := by rw [hyw]; exact (I.ker e' hpos he' _).2 ⟨w, rfl⟩

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem gen_comp : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left) (T T' : Over S) (a : T' ⟶ T) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen := by
  intro S A _ P T T' a x hx
  obtain ⟨t, ht⟩ := hx
  have e : (A ◁ a) ≫ lift (snd A T ≫ x) (fst A T) = lift (snd A T' ≫ a ≫ x) (fst A T') := by
    rw [comp_lift, whiskerLeft_snd_assoc, whiskerLeft_fst]
  rw [← e, Over.comp_left]
  exact ⟨_, LB.isGen_pullGen P _ _ t ht (A ◁ a).left⟩

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem siegKerBy_toSieg_of (hA : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ, (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left), ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1) (hB : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left) (T T' : Over S) (a : T' ⟶ T) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → ∃ t : (P.pull (lift (snd A T' ≫ a ≫ x) (fst A T')).left).Gen, t.IsGen) (hC : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1) : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e := by
  intro p _ D R _ b N S t o h M t₁ lev hl e _ hEF
  refine ⟨Obj.toSieg_ample o hl, ?_⟩
  intro T x hx
  obtain ⟨e', he', hk⟩ := o.kerP
  have hx' : x ^ e' = 1 := hk T x hx
  have hu : IsUnit ((e' : ℕ) : Γ(S, ⊤)) := by
    have h1 := (b.unit e' he').map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    have h2 := h1.map t.appTop.hom
    simpa using h2
  refine hA S o.A o.ab e' hu T x hx' e (fun k _ _ ξ => ?_)
  have hx2 := hB S o.A o.P T (Over.mk (ξ ≫ T.hom)) (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) x hx
  exact pow_eq_one_at_geom hC o e hEF k (ξ ≫ T.hom) _ hx2

end GlobalTheory.UPel.HT.KerBy

namespace GlobalTheory.UPel.HT.KerBy

theorem siegKerBy_toSieg : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e :=
  siegKerBy_toSieg_of GlobalTheory.T.pow_eq_one_of_geometric_points_torsion gen_comp GlobalTheory.T.commutatorPairing_eq_one_trivial_on_axis

end GlobalTheory.UPel.HT.KerBy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyHeightOnePrimesOfFlat
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem hart_of_flat : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B], GlobalTheory.GoodEtale.Hart A B B := by
  intro A _ _ _ _ B _ _ _ a ha m hm
  classical
  let I : Ideal A := Ideal.comap (algebraMap A B) ((Ideal.span {algebraMap A B a}).colon {m})
  have hI : ∀ u, u ∈ I ↔ ∃ m' : B, algebraMap A B u * m = algebraMap A B a * m' := by
    intro u
    simp only [I, Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc, mul_comm]⟩
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
  have hm' : ∀ s : S, ∃ m' : B, algebraMap A B s * m = algebraMap A B a * m' := fun s =>
    (hI s).1 (hS ▸ Submodule.subset_span s.2)
  choose m' hm'' using hm'
  let f : (S → A) →ₗ[A] A × (S → A) :=
    LinearMap.prod (∑ s : S, (LinearMap.proj s).smulRight (s : A)) (a • LinearMap.id)
  let x : A × (S → A) →ₗ[A] B := (LinearMap.fst A A (S → A)).smulRight m -
    ∑ s : S, ((LinearMap.proj s).comp (LinearMap.snd A A (S → A))).smulRight (m' s)
  have hxf : x ∘ₗ f = 0 := by
    apply LinearMap.ext
    intro c
    have e : ∀ s : S, (c s * s) • m = (a * c s) • m' s := by
      intro s
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, mul_assoc, hm'' s]; ring
    simp [x, f, Finset.sum_smul, e]
  obtain ⟨k, α, y, hxy, hαf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  set v := α ((1 : A), (0 : S → A)) with hvdef
  have hsv : ∀ s : S, ∀ j, (s : A) * v j ∈ Ideal.span {a} := by
    intro s j
    have e : f (Pi.single s 1) = (s : A) • ((1 : A), (0 : S → A)) + a • ((0 : A), Pi.single s 1) := by
      ext t
      · simp [f, Pi.single_apply]
      · simp [f]
    have h0 : α (f (Pi.single s 1)) = 0 := by
      simpa using congrArg (fun g => g (Pi.single s 1)) hαf
    rw [e, map_add, map_smul, map_smul] at h0
    have h1 := congrArg (fun w => w j) h0
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply] at h1
    rw [Ideal.mem_span_singleton']
    exact ⟨-(α ((0 : A), Pi.single s 1)) j, by rw [← hvdef] at h1; linear_combination -h1⟩
  have hv : ∀ j, v j ∈ Ideal.span {a} := by
    intro j
    apply GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one
    intro q hq h1
    obtain ⟨u, hu, m'', h⟩ := hm q hq h1
    refine ⟨u, hu, ?_⟩
    have huI : u ∈ I := (hI u).2 ⟨m'', by simpa [smul_eq_mul] using h⟩
    have hle : I ≤ (Ideal.span {a}).colon {v j} := by
      rw [← hS, Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul]
      exact hsv ⟨s, hs⟩ j
    have := hle huI
    rwa [Submodule.mem_colon_singleton, smul_eq_mul] at this
  choose z hz using fun j => Ideal.mem_span_singleton'.mp (hv j)
  refine ⟨y (Finsupp.equivFunOnFinite.symm z), ?_⟩
  have hv' : v = a • Finsupp.equivFunOnFinite.symm z := by
    ext j; simp [← hz j, mul_comm]
  have hmx : m = x ((1 : A), (0 : S → A)) := by simp [x]
  rw [hmx, hxy, LinearMap.comp_apply, ← hvdef, hv', map_smul, Algebra.smul_def, smul_eq_mul]

end GlobalTheory.GoodEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHartogsPropertyQuotientSpanPowRetraction
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem hartRep_one (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (a : A) (r : R)
    (h : ∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t}) :
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have hmem : ρ r ∈ Ideal.span {a} := by
    refine GlobalTheory.PrincipalHartogs.mem_span_singleton_of_forall_height_le_one a (ρ r) fun p hp hp1 => ?_
    obtain ⟨u, hu, m', hm⟩ := h p hp hp1
    refine ⟨u, hu, Ideal.mem_span_singleton.2 ⟨ρ m', ?_⟩⟩
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, hρa, hρa, sub_eq_zero] at hm
    exact hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 hmem
  refine ⟨algebraMap A R b, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, map_mul, hρa, hρa, hb, sub_self]

theorem hartRep (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (a : A) (ha : a ≠ 0) :
    ∀ n : ℕ, ∀ r : R, (∀ p : Ideal A, p.IsPrime → p.height ≤ 1 →
      ∃ u : A, u ∉ p ∧ ∃ m' : R, algebraMap A R u * r - algebraMap A R a * m' ∈ Ideal.span {t ^ n}) →
    ∃ r' : R, r - algebraMap A R a * r' ∈ Ideal.span {t ^ n} := by
  have hρa : ∀ b, ρ (algebraMap A R b) = b := fun b => by simpa using congrArg (fun f => f b) hρ
  have ht0 : ρ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  intro n
  induction n with
  | zero => intro r _; exact ⟨0, by simp⟩
  | succ n ih =>
    intro r hr
    obtain ⟨x, hx⟩ := hartRep_one A R ρ hρ t hker a r fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      exact ⟨u, hu, m', Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t n.succ_ne_zero) hm⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
    obtain ⟨y', hy'⟩ := ih y fun p hp hp1 => by
      obtain ⟨u, hu, m', hm⟩ := hr p hp hp1
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
      have key : t * (algebraMap A R u * y) - algebraMap A R a * (m' - algebraMap A R u * x)
          = t ^ (n + 1) * q := by
        linear_combination hq - (algebraMap A R u) * hy
      have h2 : a * ρ (m' - algebraMap A R u * x) = 0 := by
        have := congrArg ρ key
        rw [map_sub] at this
        simp only [map_mul, map_pow, ht0, hρa, zero_mul, zero_sub, zero_pow n.succ_ne_zero,
          neg_eq_zero] at this
        exact this
      have h3 : m' - algebraMap A R u * x ∈ Ideal.span {t} := by
        rw [← hker, RingHom.mem_ker]
        exact (mul_eq_zero.1 h2).resolve_left ha
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 h3
      refine ⟨u, hu, z, Ideal.mem_span_singleton.2 ⟨q, ?_⟩⟩
      have h4 : t * (algebraMap A R u * y - algebraMap A R a * z - t ^ n * q) = 0 := by
        rw [hz] at key
        linear_combination key
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h4)
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 hy'
    refine ⟨x + t * y', Ideal.mem_span_singleton.2 ⟨s, ?_⟩⟩
    linear_combination hy + t * hs

theorem hart_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [Algebra A R] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.Hart A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨r', hr'⟩ := hartRep A R ρ hρ t hker ht a ha n r fun p hp hp1 => by
    obtain ⟨u, hu, m', hm'⟩ := hm p hp hp1
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m'
    refine ⟨u, hu, s, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul,
      Ideal.Quotient.eq, Ideal.span_singleton_pow] at hm'
    exact hm'
  refine ⟨Ideal.Quotient.mk _ r', ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq, Ideal.span_singleton_pow]
  exact hr'

end GlobalTheory.GoodEtaleSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTransStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt_trans : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → HasFin D' → HasFin D := by
  first | exact @GlobalTheory.Mum.hasFin_of_finExt | exact GlobalTheory.Mum.hasFin_of_finExt | (intros; apply GlobalTheory.Mum.hasFin_of_finExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLocStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_pullback_injective_local : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R (maximalIdeal R) → AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')), Nonempty (IsPullDeg ρ D.toPre D'.toPre) → Has D → Has D' := by
  first | exact @GlobalTheory.Mum.has_pull | exact GlobalTheory.Mum.has_pull | (intros; apply GlobalTheory.Mum.has_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HdRFreeOfDvr
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DeRham

theorem hdR_free_of_dvr (H : GlobalTheory.Published.AbelianDeRham) (F : Type) [Field F] [NumberField F]
    (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Obj F 𝔠 (Sp R)) : ∃ n : ℕ, Nonempty (HdR X.A ≃ₗ[R] (Fin n → R)) := by
  letI := X.grp
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R (primDR X.A) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free R (HdR X.A) := inferInstanceAs (Module.Free R (Module.Dual R (primDR X.A)))
  haveI : Module.Finite R (HdR X.A) := inferInstanceAs (Module.Finite R (Module.Dual R (primDR X.A)))
  let b := Module.Free.chooseBasis R (HdR X.A)
  exact ⟨Fintype.card (Module.Free.ChooseBasisIndex R (HdR X.A)),
    ⟨b.equivFun.trans (LinearEquiv.funCongrLeft R R (Fintype.equivFin _).symm)⟩⟩

end GlobalTheory.DeRham
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselSmoothSectionLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hensel_smooth_section_lift : ∀ (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ (U : Over (Sp R₁)), Smooth U.hom → ∀ x₀ : Sp R ⟶ U.left, x₀ ≫ U.hom = spMap π → ∃ x : Sp R₁ ⟶ U.left, x ≫ U.hom = 𝟙 _ ∧ spMap π ≫ x = x₀ := by
  first | exact @GlobalTheory.QuotLift.exists_section_lift | exact GlobalTheory.QuotLift.exists_section_lift | (intros; apply GlobalTheory.QuotLift.exists_section_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffExistsSmallSectionDiffeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ s ∈ (A.tens B.dual).smallSec, s ≠ 0 := by
  first | exact @GlobalTheory.HSNef.le_iff_exists_smallSec | exact GlobalTheory.HSNef.le_iff_exists_smallSec | (intros; apply GlobalTheory.HSNef.le_iff_exists_smallSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.BallFinite

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_rep (P : Pair p) (a c : ℤ) : ∃ M : HermLB p, P.Rep a c M := by
  obtain ⟨hL, hA, -⟩ := GlobalTheory.T.represents_base_bundles_and_trivial k X p P
  have h1 : ∃ M : HermLB p, P.Rep a 0 M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hL
      rw [mul_one, mul_zero] at this
      exact ⟨_, this⟩
    · have := GlobalTheory.T.represents_hermitianLineBundle_dual k X p P _ _ _ (GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 1 0 P.L n hL)
      rw [mul_one, mul_zero, neg_zero] at this
      exact ⟨_, this⟩
  have h2 : ∃ M : HermLB p, P.Rep 0 c M := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A n hA
      rw [mul_one, mul_zero] at this
      exact ⟨_, this⟩
    · have := GlobalTheory.T.represents_hermitianLineBundle_dual k X p P _ _ _ (GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A n hA)
      rw [mul_one, mul_zero, neg_zero] at this
      exact ⟨_, this⟩
  obtain ⟨M₁, h₁⟩ := h1
  obtain ⟨M₂, h₂⟩ := h2
  have := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ _ _ M₁ M₂ h₁ h₂
  rw [add_zero, zero_add] at this
  exact ⟨_, this⟩

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem smallSec_tens_shift (N M : HermLB p) (t : ℝ) :
    ((N.tens M).shift (fun _ => t) fun _ => rfl).smallSec ⊆ (N.tens (M.shift (fun _ => t) fun _ => rfl)).smallSec :=
  fun u hu σ y => by
    refine le_of_eq_of_le ?_ (hu σ y)
    simp only [Weight.nsq, HermLB.tens, HermLB.shift, Weight.tens, Weight.addFn]
    congr 2
    ring

theorem bl_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t →
    ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  intro hHS k _ X _ p D hX P b s t hG a c R hC
  obtain ⟨M, hM⟩ := exists_rep P a c
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit (fun _ => P.A)).1
  have hSI := ((hC.arIso k X p D hX).2 Unit (fun _ => P.A) Φ hΦ).1 ()
  obtain ⟨m, hm⟩ := ((hHS k X p D hX P.A (M.shift (fun _ => R) fun _ => rfl) _ hG.nef hSI).1).exists
  have hA := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have hAm := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P 0 1 P.A m hA
  have hT := GlobalTheory.T.hermPairWithSections_represents_tensor k X p P _ _ _ _ _ _ hAm hM
  have hsm : (((P.A.pow m).tens M).shift (fun _ => R) fun _ => rfl).smallSec.Finite :=
    hm.subset (smallSec_tens_shift _ _ _)
  have hB : (P.Bl (m * 0 + a) (m * 1 + c) (Real.exp R)).Finite := by
    have e := (GlobalTheory.T.smallSections_twistedPower_encard_eq_ball k X p P _ _ _ hT R 0).2.2
    rw [← Set.encard_lt_top_iff, ← e]
    exact hsm.encard_lt_top
  have hs := hG.s_mem
  obtain ⟨hsH, hsn⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs.1 m
  refine (hB.preimage (f := fun f => s ^ m * f) (mul_right_injective₀ (pow_ne_zero m hG.s_ne)).injOn).subset ?_
  intro f hf
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P _ _ _ _ (s ^ m) f hsH hf.1
  refine ⟨h1, fun σ y => ?_⟩
  rw [h2, hsn]
  have n1 : P.nu 0 1 σ y s ≤ 1 := hs.2 σ y
  calc _ ≤ 1 * P.nu a c σ y f :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (nu_nonneg P 0 1 σ y s) n1) (nu_nonneg P a c σ y f)
    _ ≤ Real.exp R := by rw [one_mul]; exact (hf.2 σ y).trans (by linarith [Real.add_one_le_exp R])

end GlobalTheory.VolBr.BallFinite
end
end

