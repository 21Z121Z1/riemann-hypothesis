import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDirAlg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0017
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDir
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_char {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (T : CDVR) (io : c.F →+* T.Fr) (σ : E →+* ℂ) :
    ∃ χ : 𝓞 E →+* T.V, ∀ a : 𝓞 E, algebraMap T.V T.Fr (χ a) = io (embK c σ a) := by
  have hint : ∀ a : 𝓞 E, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c σ a) := by
    intro a
    have h1 : IsIntegral T.V ((io.comp (embK c σ)) a) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom T.V) (io.comp (embK c σ)) (RingHom.ext_int _ _)
        (RingOfIntegers.isIntegral a)
    exact IsIntegrallyClosed.isIntegral_iff.1 h1
  choose χ hχ using hint
  refine ⟨{ toFun := χ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hχ⟩ <;>
    intros <;> apply IsFractionRing.injective T.V T.Fr <;> simp [hχ]

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

attribute [local instance] Over.cartesianMonoidalCategory

variable {D : D7}

def GeneratorsSt : Prop :=
  ∀ (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (wt : WeightFamilies.Wt D j), 1 ≤ wt.n →
    letI := T.Q.H.starRing
  ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (y : IntFr (T.Q.Xo j) T.Q.c T' io), y.IsAlg →
  ∀ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io y) (P : PELUnif (maximalIdeal T'.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), (g = D.host.g 0 ∧ g' = D.host.g 1 ∨ g = D.host.g 1 ∧ g' = D.host.g 0) →
    g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 D.host.E), π * star π = (g : 𝓞 D.host.E) → π' * star π' = (g' : 𝓞 D.host.E) →
    (∃ u u' : 𝓞 D.host.E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 D.host.E, u * π' + u' * star π' = 1) →
    T.Q.l.Mb ≤ Ideal.span {π} ⊓ Ideal.span {π'} →
    ¬ IsUnit ((g : ℕ) : T'.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T'.Fr F] [Algebra T'.V F] [IsScalarTower T'.V T'.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T'.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T'.V (maximalIdeal T'.V)) (A' : PolAV (Spec (CommRingCat.of T'.Fr)))
    (G' : Over (Sp T'.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre wt.n)
    (pA : IsPowPolAV A' P.A wt.n) (pG : IsPowGrp G' C.I.G.G wt.n)
    (U' : Unif (maximalIdeal T'.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 D.host.E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 D.host.E)),
    (∀ (a : 𝓞 D.host.E) (x : D'.toPre.X) (i : Fin wt.n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 D.host.E) (i : Fin wt.n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∀ (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T'.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
    (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F wt.n (chD C.ch)),
    NuGe D' (sumQ pD.xe Q) F v g' s 0 → PullAl D' F oD' (star π) g' g s s₂ →
    w.IsGen → ζ ≠ 0 → FinOrd D' F (g' * g) p w ζ →
    QkToAkU U'.toUnifPre F (g' * g) p x → (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
    PhiRel D'.toPre F (g' * g) p w s₂ t₀ → Fam.IsSmul D'.toPre F ζ t₀ t →
    U'.toUnifPre.ExpandsG F (g' * g) σ' t →
    IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h →
  FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT →
  ∀ Ppol ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA wt) wt.n,
    letI := io.toAlgebra
    ∃ (k : ℕ) (f : Fin k → T.R j) (a : Fin k → F) (u : F),
      (∀ i, f i ∈ T.th j wt) ∧ (∀ i, 0 ≤ v (a i)) ∧
      v u = v (∏ τ : D.host.E →+* ℂ, algebraMap T'.Fr F (io (embK T.Q.c τ (star π * star π'))) ^
        (∑ i : Fin ((T.Q.Dw j).mult τ), wtA wt (τ, i))) ∧
      nabValN C.ch.B F (MvPowerSeries.map (algebraMap T'.Fr F) C.ch.h) T.Q.H.w0 (g' * g) h
          (fun ℓ : LtN (T.Q.Dw j) wt.n => ℓ.2.2)
          (fun (ℓ : LtN (T.Q.Dw j) wt.n) i => algebraMap T'.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (MvPolynomial.map ((algebraMap T'.Fr F).comp io) Ppol) =
        u * ∑ i, a i * algebraMap T'.Fr F (evI y (f i))

def GEndStatement : Prop :=
  ∀ (L : SizeData₂ D) (P : ParameterChoice' D L) (Tp : ParamsT D L P) (hK : DV.KapDef D) (T : Top D) (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (j : ℕ) (hj : InR D j),
    j < D.R.m →
    (letI := T.Q.H.starRing; IntChartEx (T.Q.Xo j) T.Q.c) →
    (letI := T.Q.H.starRing; ChartSaturated (T.Q.Xo j) T.Q.c) →
    (∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) →
    (∃ τ : D.host.E →+* ℂ, InPsi T.Q.H τ ∧
      ∀ x : 𝓞 D.host.E, ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F) = embK T.Q.c τ x) →
    WeightAlgebra.H3 L H C2 A2 CR 0 (lR Tp hK j) Tp.TO →
    (|(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)) /
        (2 * Module.finrank ℚ D.host.E) ≤ WeightFamilies.RRv D CR →
    (2 * D.R.f * D.R.m : ℝ) ^ 4 * Tp.nWn + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D L C2 A2 →
    D.R.f * D.R.r * (D.R.r + 1) ≤ Tp.nWn →
    (∀ i, (WeightAlgebra.DF (lR Tp hK j) : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < (D.host.g i : ℝ)) →
    ∀ la, (resCharOf la = D.host.g 0 ∨ resCharOf la = D.host.g 1) → ∀ (y : (recPJ h j hj).Pt la),
      (recPJ h j hj).depth (runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).S.sW (lR Tp hK j) la y ≤
        (((runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).nus la +
          WeightAlgebra.cc D L C2 A2 CR (lR Tp hK j) * (recPJ h j hj).phiC la y : ℝ) : EReal)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algDefStatement
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}

def H1algDefStatement : Prop :=
  ∀ (L : SizeData₂ D) (P : ParameterChoice' D L) (Tp : ParamsT D L P) (hK : DV.KapDef D) (T : Top D) (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (j : ℕ) (hj : InR D j),
    j = D.R.m →
    (letI := T.Q.H.starRing; IntChartEx (T.Q.Xo j) T.Q.c) →
    (letI := T.Q.H.starRing; ChartSaturated (T.Q.Xo j) T.Q.c) →
    (∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) →
    (∃ τ : D.host.E →+* ℂ, InPsi T.Q.H τ ∧
      ∀ x : 𝓞 D.host.E, ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F) = embK T.Q.c τ x) →
    WeightAlgebra.H3 L H C2 A2 CR 0 (lR Tp hK j) Tp.TO →
    D.R.f * D.R.r * (D.R.r + 1) ≤ Tp.nWn →
    ∀ la (y : (recPJ h j hj).Pt la),
      (recPJ h j hj).depth (runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).S.sW (lR Tp hK j) la y ≤
        (((runOf Tp hK (recB h.toLawsCore) hinj EX (nuWWOf T Tp hK) j).nus la : ℝ) : EReal)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEigPf
section
noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem linEigSt_holds : LinEigSt := LinEig.linEig_holds

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RPfVal

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Pj.Crude Formalism.MainNotions.ModuliIntegralCharts.H1

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem vLa_int_not_mem {a : 𝓞 K} (ha : a ∉ la.asIdeal) : vLa la (a : K) = 0 := by
  have h : (a : K) = algebraMap (𝓞 K) K a := rfl
  rw [vLa, h, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 ha]
  simp

theorem prime_mem_iff {p : ℕ} (hp : p.Prime) : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la = p := by
  constructor
  · intro hm
    by_contra hne
    have hl := resCharOf_prime la
    have hnd : ¬ resCharOf la ∣ p := fun hd =>
      hne ((Nat.prime_dvd_prime_iff_eq hl hp).1 hd)
    exact crv_not_mem la hnd hm
  · intro h
    rw [← h]
    exact crv_char_mem la

theorem padic_prime (l : ℕ) [Fact l.Prime] {p : ℕ} (hp : p.Prime) :
    padicValNat l p = if l = p then 1 else 0 := by
  split_ifs with h
  · subst h; exact padicValNat_self
  · have : Fact p.Prime := ⟨hp⟩
    exact padicValNat_primes h

theorem vLa_pPow {Q q d : ℕ} (hQ : Q ≠ 0) (hq : q.Prime) (hd : d.Prime) (a b c : ℕ) :
    vLa la (((Q ^ a * q ^ b * d ^ c : ℕ) : ℕ) : K) =
      (((a * padicValNat (resCharOf la) Q + b * (if resCharOf la = q then 1 else 0) +
        c * (if resCharOf la = d then 1 else 0)) * ramOverZ la : ℕ) : ℤ) := by
  have hl := resCharOf_prime la
  have : Fact (resCharOf la).Prime := ⟨hl⟩
  have h2 : (Q ^ a : ℕ) ≠ 0 := pow_ne_zero _ hQ
  have hq' : (q ^ b : ℕ) ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hd' : (d ^ c : ℕ) ≠ 0 := pow_ne_zero _ hd.ne_zero
  rw [crv_vLa_natCast la (Nat.mul_ne_zero (Nat.mul_ne_zero h2 hq') hd')]
  congr 2
  have e1 : padicValNat (resCharOf la) (Q ^ a) = a * padicValNat (resCharOf la) Q := by
    rw [padicValNat.pow]
  have e2 : padicValNat (resCharOf la) (q ^ b) = b * padicValNat (resCharOf la) q := by
    rw [padicValNat.pow]
  have e3 : padicValNat (resCharOf la) (d ^ c) = c * padicValNat (resCharOf la) d := by
    rw [padicValNat.pow]
  rw [padicValNat.mul (Nat.mul_ne_zero h2 hq') hd', padicValNat.mul h2 hq', e1, e2, e3,
    padic_prime _ hq, padic_prime _ hd]

theorem nat_mem_iff (n : ℕ) : ((n : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ resCharOf la ∣ n := by
  constructor
  · intro hm
    by_contra hnd
    exact crv_not_mem la hnd hm
  · rintro ⟨k, rfl⟩
    push_cast
    exact la.asIdeal.mul_mem_right _ (crv_char_mem la)

variable {D : D7} {j : ℕ}

theorem piG_mul_bar (EX : ErrX D) (i : Fin 2) :
    EX.piG i * piBarO EX i = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
  apply RingOfIntegers.coe_injective
  have h := EX.piG_norm i
  push_cast
  exact h

theorem nnW_not_mem (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∉ la.asIdeal) :
    nnW B hinj EX w ∉ la.asIdeal := by
  have hπ : ∀ i, iE D hinj B (EX.piG i) ∉ la.asIdeal ∧ iE D hinj B (piBarO EX i) ∉ la.asIdeal := by
    intro i
    have hn : iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 B.KO) := by
      rw [← map_mul, piG_mul_bar, map_natCast]
    exact ⟨fun hm => hg i (hn ▸ la.asIdeal.mul_mem_right _ hm),
      fun hm => hg i (hn ▸ la.asIdeal.mul_mem_left _ hm)⟩
  have : nnW B hinj EX w ∈ la.asIdeal.primeCompl := by
    unfold nnW
    exact Submonoid.prod_mem _ fun i _ =>
      Submonoid.mul_mem _ (Submonoid.pow_mem _ (hπ i).1 _) (Submonoid.pow_mem _ (hπ i).2 _)
  exact this

theorem vAdd_sW (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hg : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∉ la.asIdeal) :
    ((vAdd la (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) : ℤ) : ℝ) =
      (ramOverZ la : ℝ) * clOf w la := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hq2 : D.host.q ≠ 2 := by omega
  have hd2 : D.host.d ≠ 2 := by omega
  have hqd : D.host.q ≠ D.host.d := by omega
  have hnn := nnW_not_mem B hinj EX w la hg
  have hnn0 : ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 := fun h =>
    hnn ((NumberField.RingOfIntegers.coe_eq_zero_iff.1 h) ▸ la.asIdeal.zero_mem)
  have hP : pPow D (c2 D w) (cHalf w) (cHalf w) = D.host.QS ^ c2 D w * D.host.q ^ cHalf w * D.host.d ^ cHalf w := rfl
  have hN0 : ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) ≠ 0 := by
    rw [hP]
    exact_mod_cast Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
      (pow_ne_zero _ hd.ne_zero)
  have hc : (((nnW B hinj EX w * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : 𝓞 B.KO)) : 𝓞 B.KO) : B.KO) =
      ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) := by
    show algebraMap (𝓞 B.KO) B.KO _ = _
    rw [map_mul, map_natCast]
  show ((vLa la _ : ℤ) : ℝ) = _
  rw [hc, crv_vLa_mul la hnn0 hN0, vLa_int_not_mem la hnn, hP, vLa_pPow la D.host.QS_pos.ne' hq hd]
  unfold clOf
  rw [show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
  simp only [nat_mem_iff la D.host.QS, prime_mem_iff la hq, prime_mem_iff la hd]
  by_cases hS : resCharOf la ∣ D.host.QS
  · have h1 : resCharOf la ≠ D.host.q := fun h => D.host.q_not_dvd_QS (h ▸ hS)
    have h2 : resCharOf la ≠ D.host.d := fun h => D.host.d_not_dvd_QS (h ▸ hS)
    rw [if_pos hS, if_neg h1, if_neg h2]
    generalize padicValNat (resCharOf la) D.host.QS = m
    push_cast; ring
  · rw [if_neg hS, padicValNat.eq_zero_of_not_dvd hS]
    split_ifs <;> (try (exfalso; omega)) <;> (try (exfalso; tauto)) <;> push_cast <;> ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.RPfVal
end
end

