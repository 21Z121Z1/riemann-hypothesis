import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.IdemDataBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import Formalism.LocalRingCardinality.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValueRamifiedOfLifts
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Jv

variable (T : CDVR) (e : ℕ)

theorem nval_alg_nonneg (r : T.V) : (0 : EReal) ≤ nval T.V e (algebraMap T.V T.Fr r) := by
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]
    exact le_top
  · rw [nval_of_ne hr]
    have hv0 : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by
      unfold Formalism.L2.Pj.vV Formalism.L2.Pj.valV
      have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
        (IsDiscreteValuationRing.maximalIdeal T.V) r
      have hne : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V))
          (algebraMap T.V T.Fr r) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
      have hlog := (WithZero.log_le_log hne one_ne_zero).mpr hle
      rw [WithZero.log_one] at hlog
      linarith
    have hv : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by exact_mod_cast hv0
    exact EReal.coe_nonneg.mpr (div_nonneg hv (Nat.cast_nonneg e))

def Jv (c : ℝ) : Submodule T.V T.Fr where
  carrier := {x | (((-c : ℝ)) : EReal) ≤ nval T.V e x}
  add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (nval_add e a b)
  zero_mem' := by
    show _ ≤ nval T.V e 0
    rw [nval_zero]
    exact le_top
  smul_mem' := fun r x hx => by
    show _ ≤ nval T.V e (r • x)
    rw [Algebra.smul_def, nval_mul]
    exact hx.trans (le_add_of_nonneg_left (nval_alg_nonneg T e r))

theorem one_mem_Jv {c : ℝ} (hc : 0 ≤ c) : (1 : T.Fr) ∈ Jv T e c := by
  show ((-c : ℝ) : EReal) ≤ nval T.V e 1
  have h1 := Formalism.L2.Pj.vV_mul (V := T.V) (K' := T.Fr) (x := 1) (y := 1) one_ne_zero one_ne_zero
  rw [mul_one] at h1
  have h0 : vV T.V (1 : T.Fr) = 0 := by omega
  rw [nval_of_ne one_ne_zero, h0]
  simp only [Int.cast_zero, zero_div]
  exact_mod_cast neg_nonpos.mpr hc

theorem mem_Jv_pow {c : ℝ} (_hc : 0 ≤ c) : ∀ (m : ℕ) (x : T.Fr), x ∈ Jv T e c ^ m →
    (((-((m : ℝ) * c)) : ℝ) : EReal) ≤ nval T.V e x := by
  intro m
  induction m with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    simp only [Nat.cast_zero, zero_mul, neg_zero, EReal.coe_zero]
    exact nval_alg_nonneg T e r
  | succ m ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · rw [nval_mul]
      have h1 := ih a ha
      have h2 : ((-c : ℝ) : EReal) ≤ nval T.V e b := hb
      calc (((-(((m + 1 : ℕ) : ℝ) * c)) : ℝ) : EReal)
          = (((-((m : ℝ) * c)) : ℝ) : EReal) + ((-c : ℝ) : EReal) := by
            rw [← EReal.coe_add]
            congr 1
            push_cast
            ring
        _ ≤ _ := add_le_add h1 h2
    · exact le_trans (le_min hy hz) (nval_add e y z)

end Jv

theorem two_pairMin_le {ι π : Type} [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool)
    (x : ι →₀ ℕ) : 2 * pairMin c s x ≤ ∑ l, x l := by
  unfold pairMin
  rw [Finset.mul_sum]
  calc ∑ q : π, 2 * min (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
      ≤ ∑ q : π, ((∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l) +
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        have h1 := min_le_left (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        have h2 := min_le_right (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        omega
    _ = ∑ l, x l := by
        simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_eq_single (c l)]
        · cases s l <;> simp
        · intro b _ hb
          have hb' : c l ≠ b := fun h => hb h.symm
          simp [hb']
        · intro h
          exact absurd (Finset.mem_univ _) h

theorem sum_pairMin_le {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ) {π : Type} [Fintype π] [DecidableEq π]
    (c : T → π) (s : T → Bool) (a : T → ℕ → ℕ) (mo : Formalism.L2.Pj.Letter T rr n →₀ ℕ)
    (hrow : ∀ (σ : T) (i : Fin (rr σ)), ∑ b : Fin n, mo ⟨σ, i, b⟩ = a σ i) :
    ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      (∑ σ, ∑ i : Fin (rr σ), a σ i) / 2 := by
  have h2 : 2 * ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      ∑ σ, ∑ i : Fin (rr σ), a σ i := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ b : Fin n, ∑ ℓ : (Σ τ : T, Fin (rr τ)), colL rr n mo b ℓ :=
          Finset.sum_le_sum (fun b _ => two_pairMin_le _ _ _)
      _ = ∑ ℓ : (Σ τ : T, Fin (rr τ)), ∑ b : Fin n, mo ⟨ℓ.1, ℓ.2, b⟩ := by
          rw [Finset.sum_comm]
          rfl
      _ = ∑ σ, ∑ i : Fin (rr σ), a σ i := by
          rw [Fintype.sum_sigma]
          exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun i _ => hrow σ i))
  omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigenLiftsOfDirectionsBiext
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def ChartDirectionsEigen : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      letI := io.toAlgebra
      ∀ (ℓ : Lt1 (T.Q.Dw j)) (a : 𝓞 D.host.E),
        (Matrix.of fun i m => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), m) 1) (C.ch.B.A.act a i)).mulVec
          (C.ch.uvec ℓ) = io (embK T.Q.c ℓ.1 a) • C.ch.uvec ℓ

def IntegralBiextension : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      letI := io.toAlgebra
      ∃ B : Germ.FB Tc.V (chD C.ch) (𝓞 D.host.E), B.IsCanonGauge Tc.Fr C.ch.h ∧
        ∀ a i, B.actK Tc.Fr a i = C.ch.B.A.act a i

def PrimeConductorEigenLifts : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ D.host.condN.primeFactors, ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI,
      letI := io.toAlgebra
      ∃ φ : Lt1 (T.Q.Dw j) → Fin (chD C.ch) → Tc.V, ∀ ℓ ℓ' : Lt1 (T.Q.Dw j),
        ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 →
        ∑ i, (algebraMap Tc.V Tc.Fr (φ ℓ' i) - (TB.sg1 Tc.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) * C.ch.uvec ℓ i = 0

namespace Pf.EigA

theorem idem_data {E : Type} [Field E] [NumberField E] {k V : Type} [Field k] [CommRing V] [Algebra V k]
    (ψ : E →+* k) (hint : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (algebraMap (𝓞 E) E x)) (w : V)
    (hw : algebraMap V k w * (((discr E).natAbs : ℕ) : k) = 1) :
    ∃ (n : ℕ) (b : Fin n → 𝓞 E) (c : Fin n → V),
      (∑ i, algebraMap V k (c i) * ψ (algebraMap (𝓞 E) E (b i)) = 1) ∧
      ∀ a : 𝓞 E, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap V k (c i) = ψ (algebraMap (𝓞 E) E a) * algebraMap V k (c j) := by
  classical
  obtain ⟨b, c, h1, h2⟩ := idem_data_basis ψ hint w hw
  set eq := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
  refine ⟨_, fun i => b (eq.symm i), fun i => c (eq.symm i), ?_, fun a => ?_⟩
  · rw [Equiv.sum_comp eq.symm (fun x => algebraMap V k (c x) * ψ (algebraMap (𝓞 E) E (b x)))]
    exact h1
  · obtain ⟨m, hm1, hm2⟩ := h2 a
    refine ⟨fun i j => m (eq.symm i) (eq.symm j), fun i => ?_, fun j => ?_⟩
    · rw [hm1, ← Equiv.sum_comp eq.symm (fun x => m (eq.symm i) x • b x)]
    · rw [Equiv.sum_comp eq.symm (fun x => (m x (eq.symm j) : k) * algebraMap V k (c x))]
      exact hm2 _

end Pf.EigA

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NuChainPf
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

theorem secScal_cast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (h : Y ⟶ G.left)
    (k : ℕ) {L1 L2 : RigLB G} (e : L1 = L2)
    (s1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ))))
    (σ1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (hs : GeneratorPullback.SecScal L1.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) s1 (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ1 h 1) :
    GeneratorPullback.SecScal L2.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) (e ▸ s1) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (e ▸ σ1) h 1 := by
  subst e; exact hs

theorem nuReg : NuRegSt := by
  intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ k hk F hF
  obtain ⟨s, Ex, htie, hexp, hnu⟩ := hF
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  obtain ⟨σ', hσ'⟩ := nuExt V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U k hk s Ex hexp hnu
  have hsc := secScal_cast (pullback.fst t.G.hom (Out.jK V)) k P.bundle s σ' hσ'
  refine ⟨P.bundle ▸ σ', fun Z r zp hzp z J J' hJ hJ' => ?_⟩
  have e1 := ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ
  rw [Category.assoc, iotaK, pullback.lift_fst] at e1
  exact e1.trans (htie Z r zp hzp z J J' hJ hJ')

theorem zCast_trans {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ k₃ : ℤ} (h : k₁ = k₂) (h' : k₂ = k₃)
    (F : LB.Sec (LPow A L k₁ T)) : zCast A h' (zCast A h F) = zCast A (h.trans h') F := by
  subst h; subst h'; rfl

theorem zCast_self {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k : ℤ} (h : k = k)
    (F : LB.Sec (LPow A L k T)) : zCast A h F = F := rfl

theorem regUnif_of (hN : NuDataSt) (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := by
  intro E _ _ _ H V _ _ _ _ _ t P hTor θ _ M hMu tK m w hrig θK hθK t₀ F hVt
  obtain ⟨ϖ, Q, vK, hϖ, hQ, hvK⟩ := hN E H V t P
  obtain ⟨t', α₀, α, s₁, U, hok1, hok2, hα₀, hnorm, hαc, htw, hsym, hact⟩ := hVt
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMu
    · exact h
  have n0 := hT E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig θ θK hθK
  have n0' : NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm (zCast tK.G Nat.cast_one θK)) := by
    rw [zCast_trans, zCast_self]; exact n0
  have n1 := hM E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig M hM1 (zCast tK.G Nat.cast_one θK) α₀ α s₁ n0'
    hα₀ hnorm hαc htw
  have hk : 0 < M ^ 2 := pow_pos hM1 2
  have n2 := hF E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig ((M : ℤ) ^ 2) (M ^ 2) (natCast_sq M) hk s₁ F t' U n1
    (by first | exact hok1 | exact hok2) hsym hact
  exact nuReg E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig (M ^ 2) hk (zCast tK.G (natCast_sq M) F) n2

theorem nuData : NuDataSt := by
  intro E _ _ _ H V _ _ _ _ _ t P
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using fun χ => QForm.exists_QVal hϖ P.D χ
  exact ⟨ϖ, Q, TG.vK hϖ, hϖ, hQ, TG.valOver_vK hϖ⟩

theorem regUnif_of' (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := regUnif_of nuData hT hM hF

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NzdOfCompOfConn
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

theorem nzdOfComp_of_conn
    (hc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), IsPreconnected X.dom) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.NZDOfCompSt := by
  intro D T h j hj w F σ hσ hne w' G hFG
  have hFc : (F : T.R j) ∈ T.C j w := cutR_le T.C j w F.2
  have hGc : (G : T.R j) ∈ T.C j w' := cutR_le T.C j w' G.2
  have hmem : (F : T.R j) * (G : T.R j) ∈ cutR T.C j (WeightAlgebra.wadd w w') := by
    rw [cutR_eq T.C hj]; exact h.toLawsCore.mul j hj w w' _ hFc _ hGc
  have hval : (F : T.R j) * (G : T.R j) = 0 := by
    have h1 : incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G = 0 := hFG
    rw [incG_mul deg (cutR T.C j) (deg_wadd w w') F G hmem] at h1
    have h2 := incG_inj deg (cutR T.C j) _ (h1.trans (map_zero _).symm)
    exact congrArg Subtype.val h2
  have hU := h.unf j hj σ hσ
  have hrd : rdU (T.U j σ) (F : T.R j) * rdU (T.U j σ) (G : T.R j) = 0 := by
    rw [← rdU_mul, hval, map_zero]
  have hFs := fun k => (hU.2.2.2.2.1 _ _ (dom_wtA w) _ (cusp_le_sec _ _ _ _ _ hFc) k).1
  have hGs := fun k => (hU.2.2.2.2.1 _ _ (dom_wtA w') _ (cusp_le_sec _ _ _ _ _ hGc) k).1
  have hG0 : ∀ k, ∀ y ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) (G : T.R j) k y = 0 := by
    intro k
    obtain ⟨x0, hx0, hx0ne⟩ := hne k
    exact eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom _) (hc _ _ _) (hFs k) (hGs k)
      (fun y _ => congrFun (congrFun hrd k) y) hx0 hx0ne
  have hsup : supN (T.U j σ).X (laU (T.U j σ) (wtA w') w'.n) (rdU (T.U j σ) (G : T.R j)) = 0 := by
    unfold supN supE
    have h0 : ∀ p : FPt (T.U j σ).X, ENNReal.ofReal (((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA w') w'.n p.1)
        (rdU (T.U j σ) (G : T.R j) p.1) p.2) = 0 := by
      intro p
      unfold Data.pnorm
      rw [hG0 p.1 p.2 p.2.2]
      simp
    simp [h0]
  exact Subtype.ext (h.supDef j hj _ _ (dom_wtA w') σ hσ _ hGc hsup)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cuspTie : CuspTieSt := by
  intro D T h j hj w hlast x P hP f hf
  exact h.thCusp j hj _ _ (dom_wtA w) hlast f ⟨x, P, hP, hf⟩

lemma sum_extendByZero_le_sum {p : ℕ} (g : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 g i ≤ ∑ i : Fin p, g i := by
  unfold ext0
  have hF : ∀ n : ℕ, (∑ i : Fin n, (if h : (i : ℕ) < p then g ⟨i, h⟩ else 0)) =
      ∑ k ∈ Finset.range n, (if h : k < p then g ⟨k, h⟩ else 0) := fun n =>
    Fin.sum_univ_eq_sum_range (fun k => if h : k < p then g ⟨k, h⟩ else 0) n
  have hg : (∑ i : Fin p, g i) = ∑ i : Fin p, (if h : (i : ℕ) < p then g ⟨i, h⟩ else 0) :=
    Finset.sum_congr rfl (fun i _ => by simp)
  rw [hg, hF m, hF p]
  calc ∑ k ∈ Finset.range m, (if h : k < p then g ⟨k, h⟩ else 0)
      ≤ ∑ k ∈ Finset.range (max m p), (if h : k < p then g ⟨k, h⟩ else 0) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left m p))
    _ = ∑ k ∈ Finset.range p, (if h : k < p then g ⟨k, h⟩ else 0) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (le_max_right m p))
        intro k _ hk
        rw [Finset.mem_range] at hk
        rw [dif_neg hk]

open Classical in
lemma sum_single_embedding_extend_le {E : Type} [Field E] [NumberField E] (e : E →+* ℂ) (mult : (E →+* ℂ) → ℕ) {p : ℕ}
    (g : Fin p → ℕ) :
    ∑ τ : E →+* ℂ, ∑ i : Fin (mult τ), (if τ = e then ext0 g i else 0) ≤ ∑ i, g i := by
  rw [Finset.sum_eq_single e]
  · simp only [eq_self_iff_true, if_true]
    exact sum_extendByZero_le_sum g (mult e)
  · intro τ _ hτ
    exact Finset.sum_eq_zero (fun i _ => if_neg hτ)
  · intro h
    exact absurd (Finset.mem_univ e) h

open Classical in
lemma DF_wtA_le {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H)
    (w : WeightFamilies.Wt D j) :
    DF Dw (wtA w) ≤ ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  have hswap : ∀ F : (τ : D.host.E →+* ℂ) → Fin (Dw.mult τ) → D.what₂.Tau → ℕ,
      ∑ τ, ∑ i : Fin (Dw.mult τ), ∑ t, F τ i t = ∑ t, ∑ τ, ∑ i : Fin (Dw.mult τ), F τ i t := by
    intro F
    calc ∑ τ, ∑ i : Fin (Dw.mult τ), ∑ t, F τ i t = ∑ τ, ∑ t, ∑ i : Fin (Dw.mult τ), F τ i t :=
          Finset.sum_congr rfl (fun τ _ => Finset.sum_comm)
      _ = ∑ t, ∑ τ, ∑ i : Fin (Dw.mult τ), F τ i t := Finset.sum_comm
  unfold Formalism.L2.Pj.DF wtA
  rw [hswap]
  apply Finset.sum_le_sum
  intro t _
  simp only [Finset.sum_add_distrib]
  exact add_le_add (by convert sum_single_embedding_extend_le (DV.tauEmb D t) Dw.mult (w.aP t))
    (by convert sum_single_embedding_extend_le (conjEmb (DV.tauEmb D t)) Dw.mult (w.aM t))

theorem deg : DegSt := by
  intro D T h j hj w P hP
  have hrow := hP.1.2.2
  have h1 : P.totalDegree ≤ DF (T.Q.Dw j) (wtA w) := by
    refine Finset.sup_le (fun m hm => ?_)
    rw [Finsupp.sum_fintype _ _ (by simp)]
    rw [Fintype.sum_sigma]
    refine le_of_eq (Finset.sum_congr rfl (fun σ _ => ?_))
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => hrow m hm σ i)
  have h2 := DF_wtA_le (T.Q.Dw j) w
  have h3 : (((∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) : ℕ)) : ℝ) = absA w := by
    simp [absA]
  rw [← h3]
  exact_mod_cast h1.trans h2

theorem dimPos_fr (D : D7) : 1 ≤ D.R.f ∧ 1 ≤ D.R.r := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    exact le_trans (by omega : 1 ≤ D.R.m) h2
  · have h3 := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupGenTies
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem coprime_two_sq {R : Type*} [CommRing R] (I J : Ideal R) (M : ℕ) (hM : Odd M) (hI : (M : R) ∈ I)
    (hIJ : I ⊔ J = ⊤) : IsCoprime (Ideal.span {(2 : R)} * J ^ 2) I := by
  have h2 : IsCoprime (Ideal.span {(2 : R)}) I := by
    rw [Ideal.isCoprime_iff_exists]
    obtain ⟨k, hk⟩ := hM
    refine ⟨-(2 * (k : R)), ?_, (M : R), hI, ?_⟩
    · exact (Ideal.span {(2 : R)}).neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2))
    · rw [hk]; push_cast; ring
  have hJ : IsCoprime J I := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hIJ
  exact IsCoprime.mul_left h2 hJ.pow_left

theorem exists_rep {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (A B : Ideal R) (h : IsCoprime A B)
    (x : N) : ∃ x2 : N, x2 ∈ A • (⊤ : Submodule R N) ∧ x2 - x ∈ B • (⊤ : Submodule R N) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  refine ⟨a • x, Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩
  have hx : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
  have e : a • x - x = -(b • x) := by
    calc a • x - x = a • x - (a • x + b • x) := by rw [hx]
      _ = -(b • x) := by abel
  rw [e]
  exact Submodule.neg_mem _ (Submodule.smul_mem_smul hb Submodule.mem_top)

theorem M_mem_Mb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
  have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h1
  exact Ideal.mul_le_left h1

theorem coprime_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    IsCoprime (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) l.Mb :=
  coprime_two_sq l.Mb _ l.M l.odd (M_mem_Mb l) l.coprime

theorem rep_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (l : Level H)
    (x : Dw.La) :
    ∃ x2 : Dw.La,
      x2 ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La) ∧
      x2 - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
  exists_rep _ _ (coprime_level l) x

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

