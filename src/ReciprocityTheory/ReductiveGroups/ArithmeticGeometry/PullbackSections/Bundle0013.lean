import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0030
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FinExtIn
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

def CDVRExtSt : Prop :=
  ∀ (T : CDVR), T.FinRes → ∀ (K : Type) [Field K] (jK : T.Fr →+* K),
    (letI := jK.toAlgebra; FiniteDimensional T.Fr K) →
    ∃ (T' : CDVR) (κ : K →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : T.Fr, a ≠ 0 → vV T'.V (κ (jK a)) = (e' : ℤ) * vV T.V a) ∧ T'.FinRes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IntFrBCSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (yI : IntFr Xo c T io) (iT : T.Fr →+* T'.Fr) (e' : ℕ), 0 < e' →
    (∀ a : T.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV T.V a) →
    ∃ yI' : IntFr Xo c T' (iT.comp io),
      letI := io.toAlgebra
      letI := (iT.comp io).toAlgebra
      ∃ φ : T.Fr →ₐ[c.F] T'.Fr, φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1

def CoverPtSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV T'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (io₂ : (T.dδ j n).c₂.F →+* T'.Fr), (∀ (a : (T.dδ j n).c₂.F) (b : T.Q.c.F), (a : ℂ) = b → io₂ a = iT (io b)) ∧
      ∃ (yI₂ : IntFr (T.dδ j n).Xo₂ (T.dδ j n).c₂ T' io₂), yI₂.IsAlg ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        letI := io₂.toAlgebra
        ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)) (φ : Tc.Fr →ₐ[T.Q.c.F] T'.Fr), φ.toRingHom = iT ∧
          FrMap φ yI.1 yI'.1 ∧ FrOver (T.dδ j n) yI₂.1 yI'.1

def ShortSplitSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ) (Λ : GenLat D.host.E n) (N : ℕ),
    Λ.Unimod → badN D ≠ 0 → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j n).l₂.M → Λ.LevOK N (T.dδ j n).l₂.M →
    ∀ (K : Type) [Field K] [Algebra (T.dδ j n).c₂.F K] (y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ K),
    ∃ (K' : Type) (_ : Field K') (jK : K →+* K'), (letI := jK.toAlgebra; FiniteDimensional K K') ∧
      ∀ (L : Type) [Field L] [Algebra (T.dδ j n).c₂.F L] (ψ : K →ₐ[(T.dδ j n).c₂.F] L),
        (∃ ψ' : K' →+* L, ψ'.comp jK = ψ.toRingHom) →
        ∀ yL : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ L, FrMap ψ y yL →
        ∃ (z : Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin n →
              (ptO (T.dδ j n).Xo₂ yL.x ⟶ (T.dδ j n).Xo₂.univ.t.G))
          (tp : (Fin n → LevQ (T.Q.Dw j) (T.dδ j n).l₂) → Fin n →
              (ptO (T.dδ j n).Xo₂ yL.x ⟶ (T.dδ j n).Xo₂.univ.t.G))
          (F : (Fin n → LevQ (T.Q.Dw j) (T.dδ j n).l₂) → Fin (Λ.zCard N ((T.Q.Dw j).p + (T.Q.Dw j).q)) → Fin n →
              LB.Sec (LPow (T.dδ j n).Xo₂.univ.t.G (T.dδ j n).Xo₂.univ.t.PP.L ((N : ℤ) ^ 2)
                (ptO (T.dδ j n).Xo₂ yL.x))),
          ShortData Λ N yL z tp F

def VtSplitSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (n : ℕ) (x : Fin n → (T.Q.Dw j).La)
    (K : Type) [Field K] [Algebra T.Q.c.F K] (y : FrPt (T.Q.Xo j) T.Q.c K),
    ∃ (K' : Type) (_ : Field K') (jK : K →+* K'), (letI := jK.toAlgebra; FiniteDimensional K K') ∧
      ∀ (L : Type) [Field L] [Algebra T.Q.c.F L] (ψ : K →ₐ[T.Q.c.F] L), (∃ ψ' : K' →+* L, ψ'.comp jK = ψ.toRingHom) →
        ∀ yL : FrPt (T.Q.Xo j) T.Q.c L, FrMap ψ y yL →
        ∃ F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yL.x)),
          ∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yL.s (levPt (T.Q.Xo j) yL.x (x b)) (F b)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def HarmonicValueAtIntegralPoint : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      ∃ (T' : CDVR) (io' : T.Q.c.F →+* T'.Fr) (e' : ℕ) (yI' : IntFr (T.Q.Xo j) T.Q.c T' io'),
        OverLa la T'.V io' e' ∧ yI'.IsAlg ∧
        ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io' yI') (P' : MvPolynomial (LtN (T.Q.Dw j) w.n) T'.Fr)
          (g : Fin w.n → Germ.PS T'.Fr 1 (chD C.ch)),
          P' ∈ FFV (Dw := T.Q.Dw j) T' (wtA w) w.n ∧ (∀ b, IsIntPS T' (g b)) ∧
          letI := io'.toAlgebra
          nval Tc.V e (evI yI f) = nval T'.V e' (∑ mo ∈ P'.support, P'.coeff mo *
            ∏ b, C.ch.B.nabVal T'.Fr C.ch.h T.Q.H.w0 (T.Q.l.M ^ 2) (g b) C.ch.uvec
              (MvPolynomial.monomial (colOf mo b) 1))

theorem coprime_of_mod_one {g p : ℕ} (h : g % p = 1) : Nat.Coprime g p := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]

theorem g_coprime_ram (D : D7) (k : Fin 2) (p : ℕ) (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  apply coprime_of_mod_one
  rcases hp with rfl | rfl | rfl
  · have h2 : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ D.host.QS * D.host.q * D.host.d from
      (h2.mul_right _).mul_right _), hc]
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.d, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
      ⟨D.host.QS * D.host.q, by ring⟩), hc]
    exact Nat.mod_eq_of_lt (by omega)

theorem M_not_mem_of_ram (D : D7) (T : Top D) (h : LawsP T) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (p : ℕ)
    (hp : p ∈ ({2, D.host.q, D.host.d} : Finset ℕ)) (hpl : (p : 𝓞 T.Q.c.F) ∈ la.asIdeal) :
    ((T.Q.l.M : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal := by
  intro hmem
  rw [h.toLawsCore.pins.2.1.1, Nat.cast_mul] at hmem
  rcases la.isPrime.mem_or_mem hmem with h0 | h1
  · exact Pf.not_both_mem la (g_coprime_ram D 0 p hp) h0 hpl
  · exact Pf.not_both_mem la (g_coprime_ram D 1 p hp) h1 hpl

theorem differentExponent_nonneg (D : D7) (p : ℕ) : 0 ≤ vdP D p := by
  unfold vdP
  split_ifs
  · have h1 : (2⁻¹ : ℝ) ^ D.R.e ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : (0 : ℝ) ≤ D.R.e := Nat.cast_nonneg _
    linarith
  · norm_num

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, ext0 f i ≤ ∑ i, f i := by
  unfold ext0
  have e1 : ∑ i : Fin m, (if h : (i : ℕ) < p then f ⟨i, h⟩ else 0) =
      ∑ i ∈ Finset.range m, (if h : i < p then f ⟨i, h⟩ else 0) :=
    Fin.sum_univ_eq_sum_range (fun i => if h : i < p then f ⟨i, h⟩ else 0) m
  have e2 : ∑ i : Fin p, f i = ∑ i ∈ Finset.range p, (if h : i < p then f ⟨i, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < p then f ⟨i, h⟩ else 0) p]
    exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]
  rw [e1, e2, ← Finset.sum_filter_add_sum_filter_not (Finset.range m) (fun i => i < p)]
  have e3 : ∑ i ∈ (Finset.range m).filter (fun i => ¬ i < p), (if h : i < p then f ⟨i, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => dif_neg (Finset.mem_filter.mp hi).2
  rw [e3, add_zero]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2) (fun _ _ _ => Nat.zero_le _)

open Classical in

theorem DF_wtA_le {D : D7} (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) :
    Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ Formalism.MainNotions.WeightAlgebra.DF w := by
  show ∑ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) ≤
    ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i)
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = conjEmb (DV.tauEmb D t) then ∑ i : Fin ((T.Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [wtA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun τ _ => hsw τ, Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  exact add_le_add (sum_extendByZero_le_sum _ _) (sum_extendByZero_le_sum _ _)

theorem ramifiedValue_of_chartValues (hVC : HarmonicValueAtIntegralPoint) (hCR : ChartValueBoundRamified) : ChartValueRamified := by
  intro D T h j hj _ nab hnab w x P hP f hf Tc io yI e la ho hy p hp hpl _C
  have hM := M_not_mem_of_ram D T h la p hp hpl
  obtain ⟨T', io', e', yI', ho', hy', C, P', g, hP', hg, hval⟩ :=
    hVC D T h j hj nab hnab w x P hP f hf Tc io yI e la ho hy hM
  rw [hval]
  refine le_trans ?_ (hCR D T h j hj hnab.1 T' io' yI' e' la ho' hy' p hp hpl C (T.Q.l.M ^ 2) (wtA w) w.n P' hP' g hg)
  apply EReal.coe_le_coe_iff.2
  have hv : (0 : ℝ) ≤ ((vLa la (p : T.Q.c.F) : ℤ) : ℝ) := by exact_mod_cast Pf.vLa_nat_nonneg la p
  have hvd : 0 ≤ vdP D p := differentExponent_nonneg D p
  have hdf : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) := by
    exact_mod_cast DF_wtA_le T j w
  have hvv := mul_nonneg hv hvd
  nlinarith

theorem integralValue_of_chartValues (hVC : HarmonicValueAtIntegralPoint) (hCI : ChartValueIntegralGood) : ChartValueUnramified := by
  intro D T h j hj _ nab hnab w x P hP f hf Tc io yI e la ho hy hbad _C
  have hM : ((T.Q.l.M : ℕ) : 𝓞 T.Q.c.F) ∉ la.asIdeal := by
    intro hmem
    rw [h.toLawsCore.pins.2.1.1, Nat.cast_mul] at hmem
    rcases la.isPrime.mem_or_mem hmem with h0 | h1
    · exact hbad (D.host.g 0) (by simp) h0
    · exact hbad (D.host.g 1) (by simp) h1
  obtain ⟨T', io', e', yI', ho', hy', C, P', g, hP', hg, hval⟩ :=
    hVC D T h j hj nab hnab w x P hP f hf Tc io yI e la ho hy hM
  rw [hval]
  exact hCI D T h j hj hnab.1 T' io' yI' e' la ho' hy'
    (fun p hp => hbad p (by simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢; tauto)) C (T.Q.l.M ^ 2) (wtA w) w.n P' hP' g hg

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {X0 : Scheme.{0}} {R : Type} [CommRing R] (x0 : Sp R ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x0 Φ)

theorem epsScaleR_comp_alg (a : R) :
    (epsScaleR a).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

def scK (a : R) (p : epsR R ⟶ G') : epsR R ⟶ G' :=
  Over.homMk (spMap (epsScaleR a) ≫ p.left) (by
    rw [Category.assoc, Over.w p]
    show spMap (epsScaleR a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R))
    rw [spMap_comp_spMap, epsScaleR_comp_alg])

variable {x0}

theorem push_inj : Function.Injective (pushHom h (epsR R)) := by
  intro p q hpq
  have e : p.left ≫ Φ = q.left ≫ Φ := congrArg (fun V => V.left) hpq
  apply Over.OverMorphism.ext
  exact h.1.hom_ext e ((Over.w p).trans (Over.w q).symm)

theorem push_surj (V : overAt x0 (DualNumber R) ⟶ G) : ∃ p, pushHom h (epsR R) p = V :=
  ⟨Over.homMk (h.1.lift V.left (epsR R).hom (Over.w V)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem push_scK (a : R) (p : epsR R ⟶ G') : pushHom h (epsR R) (scK a p) = smT x0 a (pushHom h (epsR R) p) :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

theorem scK_zero_iff (p : epsR R ⟶ G') : IsTangent p ↔ scK 0 p = 1 := by
  have e0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have e1 : ((1 : epsR R ⟶ G').left) = spMap (algebraMap R (DualNumber R)) ≫ η[G'].left := by
    rw [Hom.one_def]; rfl
  have e2 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    rw [spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id _
  constructor
  · intro hp
    apply Over.OverMorphism.ext
    show spMap (epsScaleR 0) ≫ p.left = _
    rw [e1, e0, ← spMap_comp_spMap, Category.assoc, hp]
  · intro hp
    have := congrArg (fun V => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ V.left) hp
    rw [e1, ← Category.assoc, e2, Category.id_comp] at this
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ p.left = η[G'].left
    rw [← this]
    show _ = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (spMap (epsScaleR 0) ≫ p.left)
    rw [e0, ← spMap_comp_spMap]
    simp only [← Category.assoc, e2, Category.id_comp]

theorem isTangent_iff (p : epsR R ⟶ G') : IsTangent p ↔ smT x0 0 (pushHom h (epsR R) p) = 1 := by
  rw [scK_zero_iff, ← push_scK h, ← map_one (pushHom h (epsR R))]
  exact (push_inj h).eq_iff.symm

theorem isLieComb_iff {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G')) (w : epsR R ⟶ G') :
    IsLieComb c v w ↔ pushHom h (epsR R) w = combT x0 (fun i => pushHom h (epsR R) (v i)) c := by
  have hprod : ∀ u : Fin m → (epsR R ⟶ G'), pushHom h (epsR R) (List.ofFn u).prod =
      ∏ i, pushHom h (epsR R) (u i) := fun u => by
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn]; rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [hprod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show u i = scK (c i) (v i) from Over.OverMorphism.ext (hu i), push_scK]
  · intro hw
    refine ⟨fun i => scK (c i) (v i), fun i => rfl, push_inj h ?_⟩
    rw [hw, hprod]
    exact Finset.prod_congr rfl fun i _ => (push_scK h _ _).symm

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NuChain
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V]

def iotaK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V)) :
    tK.G.left ⟶ pullback t.G.hom (Out.jK V) :=
  pullback.lift m.φ tK.G.hom m.cart.1.w

def secU {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t) {k : ℕ} (s : P.U.SecK k) :
    LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => pullback.fst t.G.hom (Out.jK V)) (fun _ => (k : ℤ))) :=
  P.bundle ▸ s

def SecTieGK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (P : PELUnif (IsLocalRing.maximalIdeal V) t) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) (s : P.U.SecK k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval (secU P s) (r ≫ iotaK m) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

def NuK {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t)
    (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)) {tK : SAB H (Sp (FractionRing V))}
    (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) : Prop :=
  ∃ (s : P.U.SecK k) (Ex : Fam P.D.toPre (FractionRing V) k),
    SecTieGK m w P k F s ∧ P.U.Expands k s Ex ∧ NuGe P.D Q (FractionRing V) vK k Ex 0

end Defs

def NuDataSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t),
    ∃ (ϖ : V) (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
      Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧ ValOver ϖ (FractionRing V) vK

def ThetaNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))))
      (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ → NuK P Q vK m w 1 θK

def MulNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (N : ℕ), 1 ≤ N → ∀ (s : LB.Sec (LPow tK.G tK.PP.L 1 (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (mulA tK.G N).left] ![(N : ℤ) ^ 2, -1]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N).left] ![(N : ℤ) ^ 2, -1]))
      (s₁ : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm s) → α₀.IsGen → IsNormMul tK.G tK.PP.L tK.PP.rig N α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (mulT tK.G (𝟙_ (Over (Sp (FractionRing V)))) N) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ →
      NuK P Q vK m w (N ^ 2) (zCast tK.G (natCast_sq N) s₁)

def EndNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (π : 𝓞 E) (n k : ℕ), 0 < k → ∀ (F₁ : LB.Sec (LPow tK.G tK.PP.L ((n : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (h₁ : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w (n ^ 2) (zCast tK.G (natCast_sq n) F₁) → α₀.IsGen →
      IsNormEnd tK.G tK.PP (tK.act.act π) (k : ℤ) ((n : ℤ) ^ 2) α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (endT tK.G (𝟙_ (Over (Sp (FractionRing V)))) (tK.act.act π)) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π)
        (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ →
      NuK P Q vK m w k h₁

def FinNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (a : ℤ) (k : ℕ) (ha : a = k), 0 < k → ∀ (h hh : LB.Sec (LPow tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))))
      (b : (𝟙_ (Over (Sp (FractionRing V)))) ⟶ tK.G) (U : ThetaGrp tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))),
      NuK P Q vK m w k (zCast tK.G ha h) → b ^ k = 1 → SymLift tK.G tK.PP.L a k b U → IsActOf tK.G tK.PP.L a U h hh →
      NuK P Q vK m w k (zCast tK.G ha hh)

def NuRegSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (k : ℕ), 0 < k → ∀ F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))), NuK P Q vK m w k F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))), SecTieK m w k F σ

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThExprBCPf
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def thSum [StarRing (𝓞 E)] (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (P : MvPolynomial (LtN Dw n) c.F) (K : ℤ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x))) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (F b) (colOf m b)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

