import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BadExists
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOriginModel

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem chi_odd (H : Host E) :
    haveI : Fact H.d.Prime := ⟨H.d_prime⟩
    ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ)) (-1) = -1 := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by have := H.d_mod; omega
  have h2 : ringChar (ZMod H.d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; have := H.d_mod; omega
  rw [MulChar.ringHomComp_apply, quadraticChar_neg_one h2, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  simp

theorem L_ne (H : Host E) :
    haveI : Fact H.d.Prime := ⟨H.d_prime⟩
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d) 1 ≠ 0 := by
  haveI : Fact H.d.Prime := ⟨H.d_prime⟩
  haveI : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  apply DirichletCharacter.LFunction_apply_one_ne_zero
  intro h
  have h1 := chi_odd (E := E) H
  rw [h, MulChar.one_apply isUnit_one.neg] at h1
  norm_num at h1

theorem hostRd_pow : hostRd E ^ Module.finrank ℚ E = |(discr E : ℝ)| := by
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  unfold hostRd
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div, inv_mul_cancel₀ hn, Real.rpow_one]

theorem bad_exists (l : Tor.Level H) : ∃ bad : Finset ℕ, 2 ∈ bad ∧
    ∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M' := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hne : (2 * discr E * (l.M' : ℤ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (NumberField.discr_ne_zero E)) (by exact_mod_cast hM)
  refine ⟨(2 * discr E * (l.M' : ℤ)).natAbs.primeFactors, ?_, ?_⟩
  · rw [Nat.mem_primeFactors]
    refine ⟨Nat.prime_two, ?_, Int.natAbs_ne_zero.mpr hne⟩
    rw [← Int.natCast_dvd]
    exact ⟨discr E * (l.M' : ℤ), by push_cast; ring⟩
  · intro r
    rw [Nat.mem_primeFactors, Int.natCast_dvd]
    constructor
    · rintro ⟨hp, hd, -⟩
      exact ⟨hp, hd⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hd, Int.natAbs_ne_zero.mpr hne⟩

variable {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (D.p + D.q)}

theorem sig_pos (o : TowerOrigin Y T) : 1 ≤ D.p ∧ 1 ≤ D.q := by
  have h1 := T.j_pos
  have h2 := T.j_lt
  rw [o.j_eq] at h1 h2
  omega

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y' : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y' Sys}

theorem finite_g (o : RootOrigin Y' S RM Fx) : letI := o.g.toAlgebra; Module.Finite Fx.Ωf RM.Ω := by
  letI := o.g.toAlgebra
  have hd : 0 < o.Fl.deg := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hpos, _⟩ := o.Fl.generic
    exact hpos
  exact Module.finite_of_finrank_pos (by rw [o.g_deg]; exact hd)

theorem pi_pt_ne (o : RootOrigin Y' S RM Fx) (x : o.Re.R.X) :
    ∃ a : ℂ, a ≠ 0 ∧ (fun i => o.Re.R.lift x x ⟨o.k₀, o.ix i⟩) = a • Fx.pt (o.Re.π x) := by
  obtain ⟨a, ha⟩ := o.π_pt x
  refine ⟨a, ?_, ha⟩
  rintro rfl
  obtain ⟨hnz, -⟩ := o.Re.R.mem x x (o.Re.R.mem_U x)
  obtain ⟨i, hi⟩ := hnz o.k₀
  apply hi
  have h := congrFun ha (o.ix.symm i)
  simp only [Equiv.apply_symm_apply, zero_smul, Pi.zero_apply] at h
  exact h

theorem genPt_eq (o : RootOrigin Y' S RM Fx) : genPt Fx.ξf = genPt o.𝔐.ξ₀ := by
  have hsub : ∀ (K : Type) [Field K] (p q : PrimeSpectrum K), p = q := fun K _ p q =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans (Ideal.eq_bot_of_prime q.asIdeal).symm)
  have h1 := o.g_over
  have h2 := o.𝔐.fn_over
  unfold Dominates at h2
  rw [h1] at h2
  have h3 : Fx.ξf ((spMap o.g) (IsLocalRing.closedPoint RM.Ω)) =
      o.𝔐.ξ₀ ((Spec.map (CommRingCat.ofHom o.𝔐.fn)) (IsLocalRing.closedPoint RM.Ω)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint RM.Ω)) h2
  unfold genPt
  rw [hsub Fx.Ωf (IsLocalRing.closedPoint Fx.Ωf) ((spMap o.g) (IsLocalRing.closedPoint RM.Ω)),
    hsub o.𝔐.Ω₀ (IsLocalRing.closedPoint o.𝔐.Ω₀)
      ((Spec.map (CommRingCat.ofHom o.𝔐.fn)) (IsLocalRing.closedPoint RM.Ω))]
  exact h3

end GlobalTheory.CompanionTheory.Ar.TowerOriginModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenOfFibreId
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.M0

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

def IsGenOfFibre {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) (a : O) (w : X) : Prop :=
  a ∈ (s w).asIdeal ∧ ∀ w' : X, a ∈ (s w').asIdeal → w' ⤳ w → w' = w

def NoBdryComp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ w : Y.X, IsGenOfFibre Y.s (p : O) w → w ∈ abLocus Y.t.G

def TorsRat {W : Type} [CommRing W] [IsDomain W] (G : Over (Sp W)) [GrpObj G] (k : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Algebra (FractionRing W) F] (x : Out.TF (R := W) F ⟶ G), x ^ k = 1 →
    ∃ x₀ : Out.TK W ⟶ G, x.left = Out.jFK (R := W) F ≫ x₀.left

def QkRat {W : Type} [CommRing W] [IsDomain W] (D : Out.DegPre W) (k : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] (q : Out.QkPt D F k),
    ∃ q₀ : Out.QkPt D (FractionRing W) k, QkExt (algebraMap (FractionRing W) F) q₀ q

end GlobalTheory.CompanionTheory.Ar.M0
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
section
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar.Num
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg)

noncomputable section

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
variable {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

structure IsPreFamily (x : (Σ k, J k) → Ω) (p : ℕ) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O)
    (φ : Equiv.Perm Sg) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) : Prop where
  famM : IsLatFamily O x fun c => (D c).M
  fam : ∀ τ, IsLatFamily O x (fun c => (D c).lie τ) ∧ IsLatFamily O x (fun c => (D c).W τ) ∧
    IsLatFamily O x (fun c => (D c).om τ) ∧ IsLatFamily O x (fun c => (D c).omHT τ) ∧
    IsLatFamily O x (fun c => (D c).Gam τ) ∧ IsLatFamily O x (fun c => (D c).Del τ) ∧
    IsLatFamily O x (fun c => (D c).Th τ)
  char : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O)
  base : ∀ c, mseg x c ≠ 0 → (D c).Base (chartRing O (mseg x) c) p (algebraMap O Ω w)
  test : ∀ c, mseg x c ≠ 0 → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C]
    (RC : Subalgebra O C), IsTestPt p (chartRing O (mseg x) c) RC → ∀ χ : Sg → F →*₀ C,
      (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a →
        χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →
      ((D c).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ

variable {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

def coordLat (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) : AddSubgroup (Fin m → Ω) :=
  ⨅ (q : Cpt ξ) (_ : InChart ξ (mseg y) c q) (_ : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q),
    (L q).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom

def IsFamilyOf (y : (Σ k, J k) → Ω) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) (L L' Lc Lc' : Sg → Lat ξ V)
    (b : ∀ τ, Fin (r τ) → V) (bc : ∀ τ, Fin (s τ) → V) : Prop :=
  ∀ c, mseg y c ≠ 0 → ∀ τ, (D c).lie τ = coordLat O y (L τ) (b τ) c ∧ (D c).W τ = coordLat O y (L' τ) (b τ) c ∧
    (D c).om τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc τ) (bc τ) c) ∧
    (D c).omHT τ = dotDual (chartRing O (mseg y) c) (coordLat O y (Lc' τ) (bc τ) c)

def FamilyExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) →
    ∀ p ∈ S, HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (_hpos : 0 < D.p + D.q := by assumption),
      AtPlacesOver A Ω p fun O _ _ _ _ => ∀ t₀, ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → CMType H ⊕ CMType H)
        (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F p) (w : O)
        (σ : Sg → F →+* IsLocalRing.ResidueField O)
        (Df : (∀ k, J k) → LieLatticeData Ω F (D.p + D.q) Sg (fun τ => labelRk D (e τ)) fun τ => labelRk D (e τ).swap),
        t₀ ∈ Set.range e ∧ (∀ τ, e (φ' τ) = φ (e τ)) ∧ IsPreFamily O y p w σ φ' Df ∧
        IsFamilyOf O y Df (fun τ => 𝔐.dR (e τ)) (fun τ => 𝔐.HT p (e τ)) (fun τ => 𝔐.dR (e τ).swap)
          (fun τ => 𝔐.HT p (e τ).swap) (fun τ => b (e τ)) fun τ => b (e τ).swap

def WholeFamilyExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) →
    ∀ (_hpos : 0 < D.p + D.q := by assumption) (g : ℕ) (b : Module.Basis (Fin g) Ω 𝔐.Li), ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => ∃ (w : O) (σ : Unit → ZMod p →+* IsLocalRing.ResidueField O)
        (Df : (∀ k, J k) → LieLatticeData Ω (ZMod p) (g + g) Unit (fun _ => g) fun _ => g),
        IsPreFamily O y p w σ 1 Df ∧
        IsFamilyOf O y Df (fun _ => 𝔐.M.lat) (fun _ => 𝔐.wholeW (p ^ 𝔐.R p)) (fun _ => 𝔐.M.lat)
          (fun _ => 𝔐.wholeW (p ^ 𝔐.R p)) (fun _ => b) fun _ => b

namespace Fam

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem mem_coordLat_iff (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) (a : Fin m → Ω) :
    a ∈ coordLat O y L b c ↔ ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) →
      ∑ i, a i • b i ∈ L q := by
  simp [coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem coordLat_mono (y : (Σ k, J k) → Ω) {L L' : Lat ξ V} (h : ∀ q, L q ≤ L' q) {m : ℕ} (b : Fin m → V)
    (c : ∀ k, J k) : coordLat O y L b c ≤ coordLat O y L' b c := fun a ha =>
  (mem_coordLat_iff O y L' b c a).2 fun q h1 h2 => h q ((mem_coordLat_iff O y L b c a).1 ha q h1 h2)

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem chartRing_le_regAt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (q : Cpt ξ) (h1 : InChart ξ (mseg y) c q)
    (h2 : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) {a : Ω} (ha : a ∈ chartRing O (mseg y) c) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h1.2 j
  | algebraMap o => exact h2 o
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem smul_mem_coordLat (y : (Σ k, J k) → Ω) (L : Lat ξ V) {m : ℕ} (b : Fin m → V) (c : ∀ k, J k) {t : Ω}
    (ht : t ∈ chartRing O (mseg y) c) {a : Fin m → Ω} (ha : a ∈ coordLat O y L b c) :
    t • a ∈ coordLat O y L b c := by
  rw [mem_coordLat_iff] at ha ⊢
  intro q h1 h2
  have := (L q).smul_mem ⟨t, chartRing_le_regAt O y c q h1 h2 ht⟩ (ha q h1 h2)
  have e : ∑ i, (t • a) i • b i = t • ∑ i, a i • b i := by simp [Finset.smul_sum, mul_smul]
  rw [e]; exact this

def unitLat (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Lat ξ Ω := fun q => Submodule.span (regAt ξ q) {1}

theorem mem_unitLat (q : Cpt ξ) (a : Ω) : a ∈ unitLat ξ q ↔ a ∈ regAt ξ q := by
  rw [unitLat, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    simp [Subring.smul_def]
  · intro h
    exact ⟨⟨a, h⟩, by simp [Subring.smul_def]⟩

omit [IsDomain O] [IsDiscreteValuationRing O] [∀ k, Fintype (J k)] in

theorem mem_coordLat_unitLat (y : (Σ k, J k) → Ω) (h : CoordTie O ξ (mseg y)) (c : ∀ k, J k) (hc : mseg y c ≠ 0)
    (t : Ω) (a : Fin 1 → Ω) :
    a ∈ coordLat O y (unitLat ξ) (fun _ : Fin 1 => t) c ↔ a 0 * t ∈ chartRing O (mseg y) c := by
  rw [mem_coordLat_iff]
  simp only [Fin.sum_univ_one, smul_eq_mul, mem_unitLat]
  refine ⟨fun H => (h.ring c hc _).2 fun q hq => H q hq fun o => ?_,
    fun H q h1 h2 => chartRing_le_regAt O y c q h1 h2 H⟩
  exact (h.ring c hc _).1 (Subalgebra.algebraMap_mem _ o) q hq

omit [∀ k, Fintype (J k)] in

theorem isPreFamily_of_lattice_family_two (x : (Σ k, J k) → Ω) (p : ℕ) (w : O)
    (σ : Sg → ZMod 2 →+* IsLocalRing.ResidueField O) (φ : Equiv.Perm Sg)
    (D : (∀ k, J k) → LieLatticeData Ω (ZMod 2) n Sg r s) (h : IsLatticeFamily O x p w (fun _ a => (a.val : O)) φ D) :
    IsPreFamily O x p w σ φ D := by
  refine ⟨h.famM, h.fam, ⟨h.char.1, h.char.2.1, h.char.2.2.1⟩, h.base, fun c hc C _ _ _ _ RC hT χ _ => ?_⟩
  have := h.test c hc C RC hT
  rw [← IsScalarTower.algebraMap_apply] at this
  convert this using 3 with τ a
  have h1 : (1 : ZMod 2).val = 1 := by decide
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · simp
  · simp [h1]

omit [∀ k, Fintype (J k)] in

theorem not_isPreFamily_of_irreducible (x : (Σ k, J k) → Ω) {p : ℕ} (hp : 3 ≤ p) (hi : Irreducible (p : O)) (w : O)
    (σ : Sg → F →+* IsLocalRing.ResidueField O) (φ : Equiv.Perm Sg) (D : (∀ k, J k) → LieLatticeData Ω F n Sg r s) :
    ¬ IsPreFamily O x p w σ φ D := by
  intro h
  obtain ⟨u, hu, e⟩ := h.char.2.1
  exact not_irreducible_pow (x := w) (n := p - 1) (by omega) (e ▸ (irreducible_isUnit_mul hu).2 hi)

end Fam

end

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NotIsLineFnZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.FlatModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def baseOf {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) : c.F →+* F :=
  (Spec.preimage (y ≫ pullback.snd _ _)).hom

theorem baseOf_eq {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c} {β : c.F →+* F}
    (h : y ≫ pullback.snd _ _ = spMap β) : baseOf y = β := by
  unfold baseOf
  rw [h]
  simp [spMap]

def scale (a : c.F) (φ : FrameFn Xo c) : FrameFn Xo c := fun F _ y v w => baseOf y a * φ F y v w

variable {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {a : c.F}

theorem isLineFn_scale (ha : a ≠ 0) (h : IsLineFn U τ φ) : IsLineFn U τ (scale a φ) where
  ne F _ β y v w hf := mul_ne_zero ((map_ne_zero _).2 ha) (h.ne F β y v w hf)
  chg F _ β y v w v' w' A B h1 h2 h3 h4 := by
    simp only [scale, _root_.mul_assoc, h.chg F β y v w v' w' A B h1 h2 h3 h4]
  nat F F' _ _ f β y v w y' v' w' h1 h2 h3 h4 := by
    have hb : baseOf y' = f.comp β := baseOf_eq (by
      rw [h2, Category.assoc, h1.1, ← Spec.map_comp]; rfl)
    simp only [scale, h.nat F F' f β y v w y' v' w' h1 h2 h3 h4, hb, baseOf_eq h1.1, map_mul, RingHom.comp_apply]

theorem isFlatGen_scale {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty}
    {i : Fin FU.n} (ha : a ≠ 0) (h : IsFlatGen U τ φ FU i) : IsFlatGen U τ (scale a φ) FU i where
  mem := h.mem
  line := isLineFn_scale ha h.line
  flat := by
    obtain ⟨e, ρ, he, hc⟩ := h.flat
    refine ⟨e, (a : ℂ) * ρ, he, fun P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
    rw [← hc P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8]
    simp only [scale, baseOf_eq h3.1, _root_.mul_assoc]
    rfl

theorem hasNorms_scale (ha : a ≠ 0) (hl : IsLineFn U τ φ) {N : LogNorms c.F} (h : HasNorms U τ φ N) :
    HasNorms U τ (scale a φ)
      ⟨fun s => (LogNorms.ofElt a).inf s + N.inf s, fun p κ => (LogNorms.ofElt a).fin p κ + N.fin p κ⟩ := by
  refine ⟨fun s y v w Γ Δ h1 h2 h3 => ?_, fun p κ V K _ _ _ _ _ _ j β y v w T tK m m' h1 h2 h3 h4 h5 => ?_⟩
  · have := h.1 s y v w Γ Δ h1 h2 h3
    simp only [scale, baseOf_eq h1.1, norm_mul, LogNorms.ofElt]
    rw [Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero _).2 ha)) (norm_ne_zero_iff.2 (hl.ne _ s y v w h1))]
    linarith
  · have := h.2 p κ V K j β y v w T tK m m' h1 h2 h3 h4 h5
    simp only [scale, baseOf_eq h3.1, map_mul, norm_mul, LogNorms.ofElt]
    rw [Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero _).2 ((map_ne_zero _).2 ha)))
      (norm_ne_zero_iff.2 ((map_ne_zero _).2 (hl.ne _ β y v w h3))), this, ← h2]
    simp only [RingHom.comp_apply]
    ring

theorem inf_unique {N N' : LogNorms c.F} (h : HasNorms U τ φ N) (h' : HasNorms U τ φ N') (s : c.F →+* ℂ)
    (y : Sp ℂ ⟶ Xo.XF c) (v w Γ Δ) (h1 : IsFramed U τ s y v w)
    (h2 : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ)
    (h3 : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ) : N.inf s = N'.inf s :=
  (h.1 s y v w Γ Δ h1 h2 h3).symm.trans (h'.1 s y v w Γ Δ h1 h2 h3)

theorem isLineFn_one (hp : D.p = 0) (hq : D.q = 0) : IsLineFn U τ (fun _ _ _ _ _ => 1) where
  ne _ _ _ _ _ _ _ := one_ne_zero
  chg F _ β y v w v' w' A B _ _ _ _ := by
    have : IsEmpty (Fin D.p) := by rw [hp]; infer_instance
    have : IsEmpty (Fin D.q) := by rw [hq]; infer_instance
    simp [Matrix.det_isEmpty]
  nat _ _ _ _ f _ _ _ _ _ _ _ _ _ _ _ := (map_one f).symm

theorem not_isLineFn_zero {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v w}
    (h : IsFramed U τ β y v w) : ¬ IsLineFn U τ (fun _ _ _ _ _ => 0) := fun h' => h'.ne F β y v w h rfl

theorem epsMul_zero_comp {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {v : epsAt x ⟶ G} (hv : IsTanAt G x v) : spMap (epsMul (0 : R)) ≫ v.left = (1 : epsAt x ⟶ G).left := by
  have h0 : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext z <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 : spMap (epsMul (0 : R)) = spMap (algebraMap R (DualNumber R)) ≫
      spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    rw [h0, ← Spec.map_comp]; rfl
  rw [h1, Category.assoc]
  erw [hv]
  let k : epsAt x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
  have := congrArg (fun t => t.left) (MonObj.comp_one k (M := G))
  exact this

theorem isComb_one {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} (hv : ∀ i, IsTanAt G x (v i)) (i : Fin n) :
    IsComb ((1 : Matrix (Fin n) (Fin n) R) i) v (v i) := by
  classical
  refine ⟨fun j => if i = j then v j else 1, fun j => ?_, ?_⟩
  · by_cases h : i = j
    · have h1 : epsMul (1 : R) = RingHom.id _ := by ext z <;> simp [epsMul]
      simp [h, Matrix.one_apply, h1, spMap]
    · simp only [h, Matrix.one_apply, if_false]
      exact (epsMul_zero_comp (hv j)).symm
  · induction n with
    | zero => exact i.elim0
    | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [List.prod_eq_one, (Fin.succ_ne_zero _).symm]
      · simp only [Fin.succ_ne_zero, if_false, _root_.one_mul, Fin.succ_inj]
        exact ih (v := fun j => v j.succ) (fun j => hv _) i

open Classical in

def scaleOn (Z : Set (Xo.XF c)) (a : c.F) (φ : FrameFn Xo c) : FrameFn Xo c :=
  fun F _ y v w => (if Set.range y ⊆ Z then baseOf y a else 1) * φ F y v w

theorem range_spMap_comp {F F' : Type} [Field F] [Field F'] (f : F →+* F') (y : Sp F ⟶ Xo.XF c) :
    Set.range (spMap f ≫ y) = Set.range y := by
  have : Function.Surjective (spMap f) := fun z => ⟨default, Subsingleton.elim _ _⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, this.range_eq, Set.image_univ]

theorem isLineFn_scaleOn (Z : Set (Xo.XF c)) (ha : a ≠ 0) (h : IsLineFn U τ φ) : IsLineFn U τ (scaleOn Z a φ) where
  ne F _ β y v w hf := by
    refine mul_ne_zero ?_ (h.ne F β y v w hf)
    split_ifs
    exacts [(map_ne_zero _).2 ha, one_ne_zero]
  chg F _ β y v w v' w' A B h1 h2 h3 h4 := by
    simp only [scaleOn, _root_.mul_assoc, h.chg F β y v w v' w' A B h1 h2 h3 h4]
  nat F F' _ _ f β y v w y' v' w' h1 h2 h3 h4 := by
    have hb : baseOf y' = f.comp β := baseOf_eq (by
      rw [h2, Category.assoc, h1.1, ← Spec.map_comp]; rfl)
    have hr : Set.range y' = Set.range y := by rw [h2, range_spMap_comp]
    simp only [scaleOn, h.nat F F' f β y v w y' v' w' h1 h2 h3 h4, hb, baseOf_eq h1.1, map_mul,
      RingHom.comp_apply]
    split_ifs with p q q
    · rfl
    · exact absurd (hr ▸ p) q
    · exact absurd (hr ▸ q) p
    · simp

theorem isFlatGen_scaleOn {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty}
    {i : Fin FU.n} (Z : Set (Xo.XF c)) (ha : a ≠ 0) (h : IsFlatGen U τ φ FU i)
    (hZ : ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → ¬ Set.range y ⊆ Z) :
    IsFlatGen U τ (scaleOn Z a φ) FU i where
  mem := h.mem
  line := isLineFn_scaleOn Z ha h.line
  flat := by
    obtain ⟨e, ρ, he, hc⟩ := h.flat
    refine ⟨e, ρ, he, fun P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
    rw [← hc P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8]
    simp only [scaleOn, if_neg (hZ P y h1 h2 h3.1), _root_.one_mul]

end GlobalTheory.CompanionTheory.Ar.Fl.FlatModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def HodgeCpt.OmVB {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) : Prop :=
  ∀ p ∈ S, (𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤ ∧
    ∀ s, ((𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).map (𝔐.Vgen s).dualRestrict).IsVBOn {q | InFibre 𝔐.ξ p q}
      (labelRk D s) ⊤

def IsTowerOf (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (D.p + D.q)) : Prop :=
  ∃ o : TowerOrigin Y T, ∀ B a, (o.Or B a).𝔐.OmVB

def SplitComps {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω), IsCptGen ξ →
    ξ ≫ Y.s = spMap (cst.comp β) → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ cst.range

end GlobalTheory.CompanionTheory.Ar
end
end

