import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddCharThetaCommutatorPhaseSkewLattice
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CommPhase

theorem kap_add (D : D7) (T : Tor D) {N N' : ℕ} (x y z : VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.kap D T x (y + z) = Formalism.MainNotions.TaylorLogMetric.kap D T x y * Formalism.MainNotions.TaylorLogMetric.kap D T x z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.kap, GlobalTheory.NormSum.VacMove.hf_add_right, Complex.add_im, Complex.ofReal_add, mul_add,
    Complex.exp_add]

theorem kap_eq_one_of_int (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (m : ℤ)
    (h : (Hf D T x y).im = m) : Formalism.MainNotions.TaylorLogMetric.kap D T x y = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.kap, h]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (((m : ℝ)) : ℂ) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem chars : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}, ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), ∃ χ : AddChar ((La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) ℂ, ∀ y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), χ (y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d) := by
  intro D δ hc 𝔪 a d x hx
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d)
  have hint : ∀ y ∈ La0 D (tor0 D ⊤ δ) a d, ∃ m : ℤ, (Hf D (tor0 D ⊤ δ) x y).im = m :=
    (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hc a d _ k0).2.2.1 x hx
  set Lp := La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)
  set S := (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf Lp
  have hwd : ∀ u v : Lp, (QuotientAddGroup.leftRel S) u v →
      Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d) := by
    intro u v huv
    rw [QuotientAddGroup.leftRel_apply] at huv
    have hm : ((-u + v : Lp) : VC D a d) ∈ La0 D (tor0 D ⊤ δ) a d := AddSubgroup.mem_addSubgroupOf.mp huv
    obtain ⟨m, hm⟩ := hint _ hm
    have h1 := kap_eq_one_of_int D (tor0 D ⊤ δ) x _ m hm
    have hv : (v : VC D a d) = (u : VC D a d) + ((-u + v : Lp) : VC D a d) := by
      push_cast; abel
    rw [hv, kap_add, h1, mul_one]
  let χ : AddChar (Lp ⧸ S) ℂ :=
    { toFun := fun q => Quotient.liftOn' q (fun y : Lp => Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d)) hwd
      map_zero_eq_one' := by
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((0 : Lp) : VC D a d) = 1
        exact kap_eq_one_of_int D (tor0 D ⊤ δ) x _ 0 (by simp [Hf])
      map_add_eq_mul' := by
        intro q r
        induction q using QuotientAddGroup.induction_on
        induction r using QuotientAddGroup.induction_on
        rename_i u v
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((u + v : Lp) : VC D a d) =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) * Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d)
        push_cast
        exact kap_add _ _ _ _ _ }
  exact ⟨χ, fun y => rfl⟩

end GlobalTheory.CommPhase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverWithDualNumberDerivationsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_with_dual_number_derivations : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  first | exact @GlobalTheory.CompHS.exists_derivFrame | exact GlobalTheory.CompHS.exists_derivFrame | (intros; apply GlobalTheory.CompHS.exists_derivFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBFrame
section
set_option autoImplicit false
noncomputable section
open Polynomial WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.BRing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]
  {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  {ε : PreTilt O p}

theorem tau_mul (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (y : Ainf p O) :
    τ ε * a ε y = 0 ↔ mu ε ∣ y := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  constructor
  · intro h
    have := dvd_of_eq_zero (ε := ε) 0 y (by rw [map_zero, zero_add]; exact h)
    rw [mul_zero, zero_add, sq] at this
    exact (mul_dvd_mul_iff_left (mu_ne hv hε)).1 this
  · rintro ⟨z, rfl⟩
    rw [map_mul, ← p_τ]
    linear_combination (↑p * a ε z) * τ_sq ε

theorem tau_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x : Ainf p O) :
    τ ε ∣ a ε x ↔ mu ε ∣ x := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨u, w, rfl⟩ := gen ε b
    have h := dvd_of_eq_zero (ε := ε) x (-u) (by
      rw [hb, map_neg]; linear_combination (a ε w) * τ_sq ε)
    exact mu_dvd hv hε x (by
      have h2 : mu ε ∣ mu ε * -u := dvd_mul_right _ _
      have h3 := (dvd_pow_self (mu ε) two_ne_zero).trans h
      simpa using (dvd_add_left h2).1 h3)
  · rintro ⟨c, rfl⟩
    exact ⟨p * a ε c, by rw [map_mul, ← p_τ]; ring⟩

theorem sat (hv : v.Integers O) (b : O) (h : (p : O) * b = 0) : b = 0 := by
  have hp : (p : O) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap O C) h0
    rw [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
  haveI : IsDomain O := (algebraMap O C).domain_nontrivial |> fun _ =>
    Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  exact (mul_eq_zero.1 h).resolve_left hp

theorem smod_iff {R : Type} [CommRing R] (q : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (Ideal.span {q}) ^ n • (⊤ : Submodule R R)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton]

theorem lim_series (u0 : Ainf p O) (u : ℕ → Ainf p O) : ∃ L : Ainf p O, ∀ n,
    (p : Ainf p O) ^ n ∣ (u0 + ∑ k ∈ Finset.range n, (p : Ainf p O) ^ k * u k) - L := by
  haveI : IsAdicComplete (Ideal.span {(p : Ainf p O)}) (Ainf p O) :=
    WittVector.isAdicCompleteIdealSpanP
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : Ainf p O)})
    (fun N => u0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * u k) (by
      intro m n hmn
      rw [smod_iff, ← dvd_neg, neg_sub]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        rw [Finset.sum_range_succ, show ∀ s t w : Ainf p O, u0 + (s + t) - w = (u0 + s - w) + t
          from fun _ _ _ => by ring]
        exact dvd_add ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _))
  exact ⟨L, fun n => (smod_iff _ _ _ _).1 (hL n)⟩

theorem complete (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    IsAdicComplete (Ideal.span {(p : BR ε)}) (BR ε) := by
  haveI : IsAdicComplete (Ideal.span {(p : Ainf p O)}) (Ainf p O) :=
    WittVector.isAdicCompleteIdealSpanP
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx' : ∀ n, (p : BR ε) ^ n ∣ x := fun n => by simpa using (smod_iff _ n x 0).1 (hx n)
    obtain ⟨u, w, rfl⟩ := gen ε x
    refine eq_zero_of_dvd hv hε u w (GlobalTheory.MuDivides.dvd_of_step (p : Ainf p O) (mu ε ^ 2)
      (fun z => ∀ n, ∃ s t, z = (p : Ainf p O) ^ n * s + mu ε ^ 2 * t) ?_ _ ?_)
    · intro z hz
      obtain ⟨s, t, hst⟩ := hz 1
      refine ⟨t, s, by rw [hst]; ring, fun n => ?_⟩
      obtain ⟨s', t', hst'⟩ := hz (n + 1)
      obtain ⟨e, he⟩ := mu_sq_dvd hv hε (s - p ^ n * s') ⟨t' - t, by
        linear_combination hst' - hst⟩
      exact ⟨s', e, by linear_combination he⟩
    · intro n
      obtain ⟨c, hc⟩ := hx' n
      obtain ⟨s', t', rfl⟩ := gen ε c
      obtain ⟨e, he⟩ := dvd_of_eq_zero (ε := ε) (u - p ^ n * s') (w - p ^ n * t') (by
        simp only [map_sub, map_mul, map_pow, map_natCast]
        linear_combination hc)
      exact ⟨p * s' + mu ε * t', e, by linear_combination he⟩
  · intro f hf
    have hstep : ∀ n, ∃ c, f (n + 1) - f n = (p : BR ε) ^ n * c := fun n => by
      obtain ⟨c, hc⟩ := (smod_iff _ n (f n) (f (n + 1))).1 (hf (Nat.le_succ n))
      exact ⟨-c, by linear_combination -hc⟩
    choose c hc using hstep
    choose u w huw using fun n => gen ε (c n)
    obtain ⟨u0, w0, h0⟩ := gen ε (f 0)
    obtain ⟨LX, hX⟩ := lim_series u0 u
    obtain ⟨LY, hY⟩ := lim_series w0 w
    have hf' : ∀ N, f N = a ε (u0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * u k) +
        τ ε * a ε (w0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * w k) := by
      intro N
      induction N with
      | zero => simpa using h0
      | succ N ih =>
        have := hc N
        rw [huw N] at this
        simp only [Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast] at ih ⊢
        linear_combination this + ih
    refine ⟨a ε LX + τ ε * a ε LY, fun n => (smod_iff _ _ _ _).2 ?_⟩
    obtain ⟨e1, he1⟩ := hX n
    obtain ⟨e2, he2⟩ := hY n
    refine ⟨a ε e1 + τ ε * a ε e2, ?_⟩
    rw [hf' n]
    have h1 := congrArg (a ε) he1
    have h2 := congrArg (a ε) he2
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add] at h1 h2 ⊢
    linear_combination h1 + τ ε * h2

theorem sqz_pow {R : Type} [CommRing R] (s t : R) (ht : t * t = 0) (n : ℕ) :
    (s + t) ^ (n + 1) = s ^ (n + 1) + (n + 1) * s ^ n * t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination ((n + 1 : R) * s ^ n) * ht

theorem pow_gen (x y : Ainf p O) : (a ε x + τ ε * a ε y) ^ p =
    a ε x ^ p + p * a ε x ^ (p - 1) * (τ ε * a ε y) := by
  have hsq : (τ ε * a ε y) * (τ ε * a ε y) = 0 := by
    linear_combination (a ε y * a ε y) * τ_sq ε
  have h := sqz_pow (a ε x) (τ ε * a ε y) hsq (p - 1)
  have h1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have h2 : ((p - 1 : ℕ) : BR ε) + 1 = p := by rw [← Nat.cast_add_one, h1]
  rwa [h1, h2] at h

theorem σ_pow (b : BR ε) : (p : BR ε) ∣ σ ε b - b ^ p := by
  obtain ⟨x, y, rfl⟩ := gen ε b
  obtain ⟨z, hz⟩ := frob_congr x
  obtain ⟨d, hd⟩ := frob_xi ε
  rw [pow_gen, map_add, map_mul, σ_a, σ_a, σ_τ, hz, hd]
  refine ⟨a ε z + τ ε * a ε (frobenius y) - a ε x ^ (p - 1) * (τ ε * a ε y), ?_⟩
  simp only [map_add, map_mul, map_pow, map_natCast]
  linear_combination (-(τ ε * a ε d * a ε (frobenius y))) * p_τ ε +
    ((p : BR ε) * a ε d * a ε (frobenius y)) * τ_sq ε

theorem pd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x : BR ε) (hx : θ hε x = 0) :
    ∃ y, θ hε y = 0 ∧ x ^ p = p * y := by
  suffices h : (p : BR ε) ∣ x ^ p by
    obtain ⟨y, hy⟩ := h
    refine ⟨y, sat (p := p) hv _ ?_, hy⟩
    have := congrArg (θ hε) hy
    rw [map_pow, hx, zero_pow (Fact.out : p.Prime).ne_zero, map_mul, map_natCast] at this
    exact this.symm
  obtain ⟨u, w, rfl⟩ := gen ε x
  have hu : fontaineTheta O p u = 0 := by
    rw [map_add, map_mul, θ_a, θ_a, θ_τ, zero_mul, add_zero] at hx; exact hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1
    (by rw [← GlobalTheory.AinfXi.ker_theta hv ε (prim hε)]; exact hu)
  obtain ⟨z, hz⟩ := frob_congr (xi ε)
  obtain ⟨d, hd⟩ := frob_xi ε
  have hxi : a ε (xi ε) ^ p = p + p * τ ε * a ε d - p * a ε z := by
    rw [← map_pow, show xi ε ^ p = frobenius (xi ε) - p * z by rw [hz]; ring, hd]
    simp only [map_add, map_sub, map_mul, map_natCast]
    rw [← p_τ]
  rw [pow_gen]
  refine ⟨a ε c ^ p * (1 + τ ε * a ε d - a ε z) + a ε (c * xi ε) ^ (p - 1) * (τ ε * a ε w), ?_⟩
  rw [map_mul, mul_pow, hxi]
  ring

theorem unit_coprime (n : ℕ) (h : Nat.Coprime n p) : IsUnit (n : BR ε) := by
  rw [← a_natCast ε]
  refine IsUnit.map _ (GlobalTheory.AinfXi.witt_isUnit _ ?_)
  rw [map_natCast]
  have hu : IsUnit (n : ZMod p) := by
    have := (ZMod.unitOfCoprime n h).isUnit
    rwa [ZMod.coe_unitOfCoprime] at this
  simpa using hu.map (ZMod.castHom (dvd_refl p) (PreTilt O p))

theorem isFrame (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : QLog.IsFrame p (BQ ε) (θ hε) where
  surj y := by
    obtain ⟨x, rfl⟩ := (GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε (prim hε)).2.2.2.1 y
    exact ⟨a ε x, θ_a hε x⟩
  inj := IsLocalization.injective (M := Submonoid.powers (p : BR ε)) _ (Submonoid.powers_le.2
    (mem_nonZeroDivisors_iff.2 ⟨fun x hx => torsion_free hv hε x hx,
      fun x hx => torsion_free hv hε x (by rw [mul_comm]; exact hx)⟩))
  denom q := by
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hq⟩ := IsLocalization.surj (Submonoid.powers (p : BR ε)) q
    exact ⟨k, b, by rw [← hq, map_pow, map_natCast, mul_comm]⟩
  unit_p := by
    have := IsLocalization.Away.algebraMap_isUnit (S := BQ ε) (p : BR ε)
    rwa [map_natCast] at this
  unit_coprime := unit_coprime
  pd := pd hv hε
  sat := sat hv
  complete := complete hv hε

theorem exists_bFrame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), Nonempty (QLog.BFrame ε) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  exact ⟨QLog.BFrame.mk (BR ε) (BQ ε) (a ε) (θ hε) (σ ε) (s ε) (τ ε) (isFrame hv hε) (θ_a hε)
    (σ_a ε) (s_alg ε) σ_pow (p_τ ε) (τ_sq ε) (gen ε) (tau_mul hv hε) (tau_dvd hv hε)⟩

end GlobalTheory.BRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibresStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ t : Finset (Sp R ⟶ X.left), (∀ x ∈ t, x ≫ X.hom = 𝟙 _) → (∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap e ≫ x ≠ spMap e ≫ y) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → ∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  first | exact @GlobalTheory.SectionsSpread.pairs | exact GlobalTheory.SectionsSpread.pairs | (intros; apply GlobalTheory.SectionsSpread.pairs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedLocusHomogeneousEquationsSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_locus_homogeneous_equations_sections : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A₀ B₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H), Flat f → GlobalTheory.AbLaw.IsProjBy f → N.IsLB → ∃ (Z : Scheme.{0}) (ιZ : Z ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)), IsClosedImmersion ιZ ∧ ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p (g ≫ affπ Rg (mA * mB)) (matOf g) ↔ ∃ w : T ⟶ Z, w ≫ ιZ = g) := by
  first | (exact @GlobalTheory.FormsLocus.exists_closed_formsOK) | (exact GlobalTheory.FormsLocus.exists_closed_formsOK) | (intros; apply GlobalTheory.FormsLocus.exists_closed_formsOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmValueCharacterConductorExponents
section
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.SqNum.CondExps

theorem exists_condExps : ∀ (D : D7) [IsCMField D.host.E] {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (s : ℕ)
    (κ : D.what₂.Tau → ℕ) (χ : HChar D.host.E), IsValChar (cmPhi D) s κ (condF G.pl) ∅ χ →
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) →₀ ℕ, (∀ v, ExpAt χ v (a v)) ∧
      (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) ≤ levQ G.pl ^ 2 := by
  intro D _ T Lc sc G s κ χ hχ
  let 𝔣 : Ideal (𝓞 D.host.F) := condF G.pl
  let 𝔐 : Ideal (𝓞 D.host.E) := 𝔣.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  have hrank : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 :=
    (IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E).symm.trans
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  have hnorm𝔣 : Ideal.absNorm 𝔣 = levQ G.pl := by
    simp only [𝔣, condF, levQ, map_prod, map_pow]
  have hlev : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  have hnorm𝔐 : Ideal.absNorm 𝔐 = levQ G.pl ^ 2 := by
    rw [Ideal.absNorm_algebraMap, hrank, hnorm𝔣]
  have h𝔐0 : 𝔐 ≠ ⊥ := fun h => by
    have h' := hnorm𝔐
    rw [h, Ideal.absNorm_bot] at h'
    exact (pow_pos hlev 2).ne' h'.symm
  let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => expIn (condF G.pl) (P.under (𝓞 D.host.F))
  have hdvd : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal ^ f P ∣ 𝔐 := fun P => by
    have h1 : (P.under (𝓞 D.host.F)).asIdeal ^ f P ∣ 𝔣 := pow_multiplicity_dvd _ _
    have h2 : P.asIdeal ∣ (P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
      Ideal.dvd_iff_le.2 Ideal.map_comap_le
    obtain ⟨c, hc⟩ := h1
    calc P.asIdeal ^ f P ∣ ((P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) ^ f P :=
          pow_dvd_pow_of_dvd h2 _
      _ ∣ 𝔐 := by
          refine ⟨c.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), ?_⟩
          show 𝔣.map _ = _
          rw [hc, Ideal.map_mul, Ideal.map_pow]
  have hfin : (Function.support f).Finite := by
    refine (Ideal.finite_factors h𝔐0).subset fun P hP => ?_
    exact (dvd_pow_self _ hP).trans (hdvd P)
  refine ⟨Finsupp.ofSupportFinite f hfin, fun P => ?_, ?_⟩
  · exact (hχ.2.2.2 (P.under (𝓞 D.host.F)) P rfl).2 (Finset.notMem_empty _)
  · set a := Finsupp.ofSupportFinite f hfin
    have hJ : (a.prod fun P k => P.asIdeal ^ k) ∣ 𝔐 := by
      refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun P _ => ?_
      · exact (Ideal.isCoprime_of_isMaximal fun h => hPQ (HeightOneSpectrum.ext h)).pow
      · exact hdvd P
    have e : (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) = Ideal.absNorm (a.prod fun P k => P.asIdeal ^ k) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [e, ← hnorm𝔐]
    exact Nat.le_of_dvd (hnorm𝔐 ▸ pow_pos hlev 2) (map_dvd Ideal.absNorm hJ)

end GlobalTheory.FunObj.SqNum.CondExps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreLinearHomsPrincipalCMTriple
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.GramBaseChange

theorem exists_complex_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ → Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ (A' B' : PAT H (Sp ℂ)) (f₁' f₂' : A'.t.G ⟶ B'.t.G) (p' q' : ℕ), p' + q' = p + q ∧ (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ p') ∧ (τ H.rt ≠ H.rt0 → LieMult A'.t.act (𝟙 (Sp ℂ)) τ q')) ∧ Serre.IsLinearHom A'.t.act B'.t.act f₁' ∧ Serre.IsLinearHom A'.t.act B'.t.act f₂' ∧ ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) → WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hA f₁ f₂ hf₁ hf₂
  have hβi : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨⟨A', mA, -⟩, hA2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) A
  obtain ⟨⟨B', mB, -⟩, hB2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) B
  obtain ⟨-, -, wA, hwA⟩ := hA2 A' mA inferInstance
  obtain ⟨-, -, wB, hwB⟩ := hB2 B' mB inferInstance
  haveI := hf₁.isMonHom
  haveI := hf₂.isMonHom
  obtain ⟨f₁', hm₁, e₁⟩ := GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₁
  obtain ⟨f₂', hm₂, e₂⟩ := GlobalTheory.PairingFibre.exists_hom mA.cart mB.cart f₂
  have lin : ∀ (f : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G), Serre.IsLinearHom A.t.act B.t.act f → IsMonHom f' →
      f'.left ≫ mB.φ = mA.φ ≫ f.left → Serre.IsLinearHom A'.t.act B'.t.act f' := by
    intro f f' hf hm e
    refine ⟨hm, fun c => ?_⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · have hc := congrArg CommaMorphism.left (hf.comm c)
      simp only [Over.comp_left] at hc ⊢
      rw [Category.assoc, e, ← Category.assoc, mA.act c, Category.assoc, hc, Category.assoc, mB.act c,
        ← Category.assoc, ← Category.assoc, e]
    · simp only [Over.comp_left, Category.assoc, Over.w]
  have hlie : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult A'.t.act (𝟙 (Sp ℂ)) τ n ↔
      LieMult A.t.act (spMap (σ₁.comp (algebraMap (𝓞 K) K))) τ n := fun τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A'.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rwa [Category.id_comp] at this
  have hweil : ∀ g : 𝓞 E, WeilEq B'.t.PP.L f₁' f₂' A'.t.PP.L (A'.t.act.act g) (𝟙 _) (𝟙 (Sp ℂ)) →
      WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
    intro g h
    have := (GlobalTheory.PairingFibre.weilEq_iff (g₂ := 𝟙 _) mA.cart mA.cart mB.cart mA.cart B.t.PP.isLB A.t.PP.isLB B'.t.PP.isLB
      A'.t.PP.isLB ⟨wB, hwB.1⟩ ⟨wA, hwA.1⟩ e₁ e₂ (mA.act g) (by simp) (𝟙 (Sp ℂ))).1 h
    rwa [Category.id_comp] at this
  have hT := hA ℂ (σ₁.comp (algebraMap (𝓞 K) K)) hβi
  have hd0 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd0 (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hsq : ∀ x : ℂ, x ^ 2 = -(H.d : ℂ) → x = H.rt0 ∨ x = -H.rt0 := fun x hx =>
    sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans H.sqrt_neg_disc_sq.symm)
  have hβρ : (σ₁.comp (algebraMap (𝓞 K) K)) ρ ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  rcases hsq _ hβρ with hc | hc
  · refine ⟨A', B', f₁', f₂', p, q, rfl, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩,
      lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩
    · exact (hlie τ p).2 ((hT τ).1 (ht.trans hc.symm))
    · exact (hlie τ q).2 ((hT τ).2 (fun h => ht (h.trans hc)))
  · refine ⟨A', B', f₁', f₂', q, p, add_comm _ _, fun τ => ⟨fun ht => ?_, fun ht => ?_⟩,
      lin f₁ f₁' hf₁ hm₁ e₁, lin f₂ f₂' hf₂ hm₂ e₂, hweil⟩
    · exact (hlie τ q).2 ((hT τ).2 (fun h => hne (ht.symm.trans (h.trans hc))))
    · rcases hsq _ (hτ τ) with h | h
      · exact absurd h ht
      · exact (hlie τ p).2 ((hT τ).1 (h.trans hc.symm))

end GlobalTheory.GramBaseChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceHeckeCharacterBoundedLevelTriviaStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1 := by
  first | exact @GlobalTheory.HeckeCont.eq_one_of_cong | exact GlobalTheory.HeckeCont.eq_one_of_cong | (intros; apply GlobalTheory.HeckeCont.eq_one_of_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantWeightShiftFlatLineDet
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatShift

theorem flat_step {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) (ρ : E →+* ℂ) (i j : ℕ) (hi : i < Dw.mult ρ) (hj : j < Dw.mult ρ) :
    (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = (wtOf Dw (flatWt Dw τ) 0).1 (ρ, j) ∧
      -1 ≤ (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) := by
  simp only [wtOf, flatWt, parWt, Datum.mult] at hi hj ⊢
  split_ifs at hi hj ⊢ <;> omega

theorem exists_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  intro E _ _ _ H Dw a n τ hD ha
  refine ⟨fun x => if x.2 < Dw.mult x.1 then ((a x : ℤ) + (wtOf Dw (flatWt Dw τ) 0).1 x).toNat else 0,
    ⟨fun ρ i j hij => ?_, hD.2⟩, fun ρ i hi => ?_, ?_⟩
  · by_cases hj : j < Dw.mult ρ
    · have hi : i < Dw.mult ρ := lt_of_le_of_lt hij hj
      have h1 : a (ρ, j) ≤ a (ρ, i) := hD.1 ρ hij
      obtain ⟨e, -⟩ := flat_step Dw τ ρ i j hi hj
      simp only [if_pos hi, if_pos hj]
      omega
    · simp only [if_neg hj]; exact Nat.zero_le _
  · have h1 := ha ρ i hi
    have h2 := (flat_step Dw τ ρ i i hi hi).2
    simp only [if_pos hi]
    omega
  · funext x
    rcases x with _ | ⟨ρ, i⟩
    · simp [exZ, wtZ, wtOf_snd]
    · have h1 := ha ρ i i.2
      have h2 := (flat_step Dw τ ρ i i i.2 i.2).2
      simp only [exZ, wtZ, Prod.fst_add, Pi.add_apply, if_pos i.2]
      omega

end GlobalTheory.FlatShift
end

