import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsIsometryModPrimePow
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0049
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.OntoLat

theorem exists_tower {R L M : Type} [CommRing R] [AddCommGroup L] [AddCommGroup M] [Module R L] [Module R M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (hc : ∀ r : ℕ, 0 < r → ∀ a c : L, r • a = r • c → a = c)
    (Q : ℕ → (L →ₗ[R] M) → Prop) (hQ : ∀ n m f, Q (n * m) f → Q n f)
    (hex : ∀ n : ℕ, 0 < n → ∃ f : L →ₗ[R] M,
      ((∀ a, (∃ e, f a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f a + n • e) ∧ Q n f) :
    ∃ f : ℕ → L →ₗ[R] M, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      ∀ n : ℕ, 0 < n → Q n (f n) := by
  choose g hg using fun j : ℕ => hex _ j.factorial_pos
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj => Nat.dvd_factorial hn hj)
  have hs : ∀ n : ℕ, ∃ i : ℕ, 0 < n →
      (n ∣ i.factorial ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨i, hi⟩ := IsoTower.exists_eventually_congr U (fun j => (g j).toAddMonoidHom) hn _ (hU n hn)
      exact ⟨i, fun _ => hi⟩
  choose s hs using hs
  refine ⟨fun n => g (s n), fun n m hn hm a => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨j, h1, h2⟩ := ((hs _ (Nat.mul_pos hn hm)).2.and (hs n hn).2).exists
    obtain ⟨e1, h1⟩ := h1 a
    obtain ⟨e2, h2⟩ := h2 a
    refine ⟨e2 - m • e1, ?_⟩
    show g (s (n * m)) a = g (s n) a + _
    rw [smul_sub, ← mul_smul, ← add_sub_assoc, ← h2, h1, add_sub_cancel_right]
  · obtain ⟨r, hr⟩ := (hs n hn).1
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left (hr ▸ (s n).factorial_pos)
    obtain ⟨⟨h1, h2⟩, -⟩ := hg (s n)
    rw [hr] at h1 h2
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨e, he⟩
      have he' : g (s n) a = n • e := he
      obtain ⟨b, hb⟩ := (h1 (r • a)).1 ⟨e, by rw [map_nsmul, he', mul_comm, mul_smul]⟩
      exact ⟨b, hc r hr0 _ _ (by rw [hb, mul_comm, mul_smul])⟩
    · rintro ⟨e, rfl⟩
      exact ⟨_, map_nsmul _ _ _⟩
    · obtain ⟨a, e, h⟩ := h2 a'
      exact ⟨a, r • e, by rw [h, mul_smul]⟩
  · obtain ⟨r, hr⟩ := (hs n hn).1
    exact hQ n r _ (hr ▸ (hg (s n)).2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_valueIdeal (X : Data E r) : ∃ J : FractionalIdeal (𝓞 E)⁰ E, J ≠ 0 ∧ (∀ z ∈ J, cc z ∈ J) ∧
    ∀ L : Lt E r, SelfD X L → ∀ x, x ∈ L ↔ ∀ y ∈ L, herm X.Gm x y ∈ J := by
  set ξ : E := X.κ0 / 2 with hξ
  have hξ' : ξ = X.ξ0 ∨ ξ = -X.ξ0 := X.κ0_xi.imp (fun h => by rw [hξ, h]; ring) fun h => by rw [hξ, h]; ring
  have hξ0 : ξ ≠ 0 := by
    rcases hξ' with h | h <;> rw [h]
    exacts [X.ξ0_ne, neg_ne_zero.2 X.ξ0_ne]
  have hξc : cc ξ = -ξ := by
    have := X.ξ0_im
    rcases hξ' with h | h <;> rw [h]
    · exact this
    · simp only [cc, map_neg] at this ⊢
      rw [this]
  have hI0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ0
  have hJ : ∀ z : E, z ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ) ↔
      ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (-ξ * ((a : E) * z)) = k := by
    intro z
    rw [FractionalIdeal.mem_dual hI0]
    constructor
    · intro h a
      obtain ⟨k, hk⟩ := h ((-a) • ξ) ((FractionalIdeal.mem_spanSingleton _).2 ⟨-a, rfl⟩)
      refine ⟨k, ?_⟩
      rw [eq_intCast, Algebra.traceForm_apply, Algebra.smul_def, map_neg] at hk
      rw [hk]
      congr 1
      change _ = z * (-(a : E) * ξ)
      ring
    · intro h w hw
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hw
      obtain ⟨k, hk⟩ := h (-c)
      refine ⟨k, ?_⟩
      rw [eq_intCast, ← hk, Algebra.traceForm_apply, Algebra.smul_def]
      congr 1
      change -ξ * (((-c : 𝓞 E) : E) * z) = z * ((c : E) * ξ)
      push_cast
      ring
  have htr : ∀ z : E, Algebra.trace ℚ E (cc z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  refine ⟨_, FractionalIdeal.dual_ne_zero ℤ ℚ hI0, fun z hz => ?_, fun L hL x => ?_⟩
  · rw [hJ] at hz ⊢
    intro a
    obtain ⟨k, hk⟩ := hz (-RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a)
    refine ⟨k, ?_⟩
    rw [← hk, ← htr]
    congr 1
    have e : ((-RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a : 𝓞 E) : E) = -cc (a : E) := rfl
    rw [e]
    simp only [cc, map_mul, map_neg, IsCMField.complexConj_apply_apply] at hξc ⊢
    rw [hξc]
    ring
  · have hE : ∀ (a : 𝓞 E) (u v : Fin r → E),
        EF X (a • u) v = Algebra.trace ℚ E (-ξ * ((a : E) * herm X.Gm u v)) := fun a u v => by
      rw [EF_def, ← algebraMap_smul E, HermitianTraceFormVanishing.herm_smul_left]
    constructor
    · intro hx y hy
      rw [hJ]
      intro a
      rw [← hE]
      exact (hL.2 _).1 (L.smul_mem a hx) y hy
    · intro h
      refine (hL.2 x).2 fun y hy => ?_
      have := (hJ _).1 (h y hy) 1
      rwa [← hE, one_smul] at this

theorem exists_adelic_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (F : Type) [Field F]
    [NumberField F] [Algebra F E] (c : E ≃ₐ[F] E) (hcc : ∀ x, c x = cc x) (X : Data E r) {L L' : Lt E r}
    (hL : SelfD X L) (hL' : SelfD X L') :
    ∃ g : GL (Fin r) (AdLat.RA F E),
      (g : Matrix (Fin r) (Fin r) (AdLat.RA F E)).mulVec '' (AdLat.hat F (L : Set (Fin r → E))) =
        AdLat.hat F (L' : Set (Fin r → E)) ∧
      ∀ x y, AdLat.hermA c X.Gm ((g : Matrix (Fin r) (Fin r) (AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin r) (Fin r) (AdLat.RA F E)) *ᵥ y) = AdLat.hermA c X.Gm x y := by
  obtain ⟨J, hJ0, hJc, hJ⟩ := exists_valueIdeal X
  have h1 : ReciprocityTheory.MultiplicativeHeights.IsLattice L := ⟨hL.1, SW.TensLat.span_of_selfD X hL⟩
  have h2 : ReciprocityTheory.MultiplicativeHeights.IsLattice L' := ⟨hL'.1, SW.TensLat.span_of_selfD X hL'⟩
  have hγ := SelfDualGenus.exists_isLocalIsometry_of_modular hJ0 hJc X.Gm_herm X.Gm_herm X.Gm_det X.Gm_det h2 h1
    (hJ L' hL') (hJ L hL)
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  haveI : Module.Finite (𝓞 E) L' := Module.Finite.iff_fg.2 hL'.1
  haveI : Module.Finite ℤ L' := Module.Finite.trans (𝓞 E) L'
  obtain ⟨f, f1, f2, f3⟩ := exists_tower (R := 𝓞 E) (L := L) (M := L')
    (fun n hn a b h => by
      have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have h' : (n : E) • (a : Fin r → E) = (n : E) • (b : Fin r → E) := by
        simpa only [Nat.cast_smul_eq_nsmul, Submodule.coe_smul_of_tower] using congrArg Subtype.val h
      exact Subtype.ext (smul_right_injective _ hn' h'))
    (fun n f => ∀ a a' : L, ∃ z ∈ J, herm X.Gm (f a) (f a') - herm X.Gm a a' = n • z)
    (fun n m f h a a' => by
      obtain ⟨z, hz, e⟩ := h a a'
      exact ⟨m • z, nsmul_mem (show z ∈ (J : Submodule (𝓞 E) E) from hz) m, by rw [e, mul_smul]⟩)
    (fun n hn => by
      obtain ⟨f, hf, hf'⟩ := IsomModN.exists_isometry_mod h1 h2 (IsomModN.isLattice_ideal hJ0)
        (fun x hx y hy i _ => (hJ L' hL' x).1 hx y hy) hγ hn
      refine ⟨f, hf, fun a a' => ?_⟩
      obtain ⟨m, hm, e⟩ := hf' a a'
      exact ⟨m 0, hm 0 trivial, e⟩)
  have hh : ∀ x y : Fin r → E, (∑ a, ∑ b, x a * X.Gm a b * c (y b)) = herm X.Gm x y := fun x y => by
    simp only [herm, hcc]
  obtain ⟨g, g1, -, g3⟩ := AdLat.exists_adelic_matrix_of_tower F E r L L' f h1.1 h1.2 h2.1 h2.2 f1 f2
  refine ⟨g, g1, g3 c X.Gm J (fun x hx y hy => ?_) fun n hn x y => ?_⟩
  · rw [hh]
    exact (hJ L' hL' x).1 hx y hy
  · obtain ⟨z, hz, e⟩ := f3 n hn x y
    exact ⟨z, hz, by rw [hh, hh, ← e, add_sub_cancel]⟩

theorem exists_mov_of_selfD {D : D7} {S T : HSp D} (C : Ctx S T) {L : Lt D.host.E T.rank} (hL : SelfD C.X L) :
    ∃ g ∈ GfC T, IsMov (fmt T g) C.X.Λ L := by
  haveI := (hostOfRecord D).unram
  obtain ⟨g, g1, g2⟩ := exists_adelic_matrix D.host.F (Member.cF D)
    (Member.latHat_eq_hat_and_gram D T).2.2.2.2.2.1 C.X (SW.Lev.selfD_of_sympl C.sympl) hL
  rw [C.m.gT] at g2
  obtain ⟨k, hk, rfl⟩ := (UnitarySplit.real_finite_split D T).2.2.2.1 g g2
  refine ⟨k, hk, fun u => ?_⟩
  have e : u ∈ hatV L ↔ u ∈ (AdLat.hat D.host.F (L : Set (Fin T.rank → D.host.E)) : Set _) := Iff.rfl
  rw [e, ← g1]
  exact ⟨fun ⟨u₀, h₀, h⟩ => ⟨u₀, h₀, h.symm⟩, fun ⟨u₀, h₀, h⟩ => ⟨u₀, h₀, h.symm⟩⟩

theorem exists_trivAt_mov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ Lv : SW.Level C.X, ∀ L ∈ Lv.lats,
    ∃ g ∈ GfC T, TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
  intro D S T C Lv L hL
  obtain ⟨g, -, hg⟩ := exists_mov_of_selfD C hL.1
  exact ((GlobalTheory.T.self_dual_lattices_at_level D S T C).2 Lv g L hL.1.1 hg).2.2.2 hL

end GlobalTheory.Ker.OntoLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorOriginEqPolyDeriv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockOrigin

theorem prod_C_mul_X {σ σ' : Type} [DecidableEq σ'] (c : σ → ℂ) (f : σ → σ') (L : List σ) :
    (L.map fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)).prod =
      (L.map c).prod • MvPolynomial.monomial (Multiset.toFinsupp ((L.map f : List σ') : Multiset σ')) (1 : ℂ) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.map_cons,
      ← Multiset.cons_coe, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton,
      MvPolynomial.X, MvPolynomial.C_mul', smul_mul_smul_comm, MvPolynomial.monomial_mul, one_mul]

theorem polyDeriv_aeval_monomial {σ σ' W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (c : σ → ℂ) (f : σ → σ') (u : σ' → W) {θ : W → ℂ} (hθ : ContDiff ℂ (⊤ : ℕ∞) θ) (m : σ →₀ ℕ) (x : W) :
    polyDeriv (MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v))
      (MvPolynomial.monomial m (1 : ℂ))) u θ x =
      ((Finsupp.toMultiset m).toList.map c).prod *
        I2.itD θ ((Finsupp.toMultiset m).toList.map fun v => u (f v)) x := by
  have h1 := prod_C_mul_X (fun _ : σ => (1 : ℂ)) id (Finsupp.toMultiset m).toList
  simp only [map_one, one_mul, id, List.map_id, List.map_const',
    List.prod_replicate, one_pow, one_smul, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp] at h1
  rw [← h1, map_list_prod, List.map_map]
  have h2 : (⇑(MvPolynomial.aeval (fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v)) :
      MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ) ∘ fun v => MvPolynomial.X v) =
      fun v => MvPolynomial.C (c v) * MvPolynomial.X (f v) := by
    funext v; simp
  rw [h2, prod_C_mul_X, I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
    Multiset.toFinsupp_toMultiset]
  congr 1
  refine congrFun (I2.ct_itD_perm hθ ?_) x
  have h3 : ((Finsupp.toMultiset m).toList.map fun v => u (f v)) =
      ((Finsupp.toMultiset m).toList.map f).map u := by rw [List.map_map]; rfl
  rw [h3]
  refine List.Perm.map u ?_
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList]

theorem fvec_zero_eq_polyDeriv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (θ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℂ θ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * θ (C.zOf (C.xB B) w)) → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B G Q 0 = polyDeriv (C.toH Q) (letterDir C.X C.hr C.idx) θ 0 := by
  intro D S T C B hB G θ hθ hG Q
  obtain ⟨R, -, -, hadd, -⟩ := GlobalTheory.KerReal.real_points D S T C
  obtain ⟨-, -, -, -, hdir, -⟩ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB
  set x := C.xB B with hx0
  let f : FVar D T.rank S.rank → Harm.Var C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
    fun v => (C.m.e v.1, (rowIdx C.hr).symm v.2.1, v.2.2)
  let c : FVar D T.rank S.rank → ℂ := fun v => ((2 / fockScale D v.1 : ℝ) : ℂ)
  let u : FVar D T.rank S.rank → Fin S.rank → Fin C.g → ℂ := fun v => letterDir C.X C.hr C.idx (f v)
  let lam : FVar D T.rank S.rank → (Fin S.rank → Fin C.g → ℂ) → ℂ := fun v z =>
    -(π * ∑ k, hx C.X C.bas C.idx x (u v k) (z k))
  let Dl : FVar D T.rank S.rank → ((Fin S.rank → Fin C.g → ℂ) → ℂ) → (Fin S.rank → Fin C.g → ℂ) → ℂ :=
    fun l Φ z => lam l z * Φ z + (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))
  have hlam : ∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a := by
    intro l
    refine ⟨fun a b => ?_, fun t a => ?_⟩
    · simp only [lam, GlobalTheory.Dict.hx, Pi.add_apply, mulVec_add, star_add, dotProduct_add,
        Finset.sum_add_distrib]
      ring
    · simp only [lam, GlobalTheory.Dict.hx, Pi.smul_apply, mulVec_smul, star_smul, dotProduct_smul,
        smul_eq_mul, ← Finset.mul_sum, RCLike.star_def]
      ring
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u lam θ hlam hθ Dl (fun _ _ _ => rfl)
  let A := aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B
  have key : ∀ L : List (FVar D T.rank S.rank), ∀ w, IsRealPt w →
      L.foldr (fun i g => A i g) G w =
        gaussR C.X C.bas C.idx x (C.zOf x w) * ((L.map c).prod * L.foldr Dl θ (C.zOf x w)) := by
    intro L
    induction L with
    | nil => intro w hw; simpa using hG w hw
    | cons a L ih =>
      intro w hw
      have hd : Differentiable ℝ (L.foldr Dl θ) := (hops L).1.differentiable (by simp)
      have h := (GlobalTheory.T.annihilation_creation_periodCoordinates D S T C B hB _ (fun z => (L.map c).prod * L.foldr Dl θ z)
        (hd.const_mul _) ih a.1 (unitMap 1 (B a.1) a.2.1 a.2.2) (u a) (hdir a.1 a.2.1 a.2.2).symm w hw).2
      rw [List.foldr_cons]
      change ((fockScale D a.1 : ℂ)⁻¹) * crea (heisO C.ψ S T) C.θ a.1 (cplxO 1 (C.sB B a.1))
        (unitMap 1 (B a.1) a.2.1 a.2.2) (L.foldr (fun i g => A i g) G) w = _
      rw [h, fderiv_const_mul (hd _)]
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, _root_.smul_apply, smul_eq_mul]
      simp only [Dl, lam, c, ← hx0]
      push_cast
      ring
  have h0 : C.zOf x 0 = 0 := by
    have h1 : C.realPt 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    funext k i
    simp only [Ctx.zOf, h1, zR, Pi.zero_apply, mulVec_zero]
    split_ifs
    · simp [hermC]
    · rfl
  have hr0 : IsRealPt (0 : WO S T) := by
    unfold IsRealPt
    ext i j
    simp
  have hg0 : gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := by
    simp [gaussR, GlobalTheory.Dict.hx]
  have hsm := I2.contDiff_of_diff hθ
  induction Q using MvPolynomial.induction_on' with
  | add P P' hP hP' =>
    rw [map_add, I2.polyDeriv_add, ← hP, ← hP', Ctx.fvec, map_add]
    rfl
  | monomial m a =>
    have e : MvPolynomial.monomial m a = a • MvPolynomial.monomial m (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, I2.polyDeriv_smul, Ctx.fvec, map_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    have h2 : pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B G
        (MvPolynomial.monomial m (1 : ℂ)) = opPow A m G := by
      have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
        (fun k => opPow A k G) m
      rwa [MvPolynomial.coe_basisMonomials] at this
    rw [h2, opPow, key _ 0 hr0, h0, hg0, one_mul, (hops _).2]
    refine Eq.trans ?_ (polyDeriv_aeval_monomial c f _ hsm m 0).symm
    congr 1
    rw [I2.ct_iter_eq_itD_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map _ u

end GlobalTheory.Ker.FockOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaLevelDataFormsSystemStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianThetaLevelData_forms_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ μ : GL (Fin r) E → Lt E r → ℂ, (∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L)) → IsSystem X bas idx M D.grp D.lats (D.phi bas hn v₀) μ := by
  first | exact @GlobalTheory.SW.isSystem_level | exact GlobalTheory.SW.isSystem_level | (intros; apply GlobalTheory.SW.isSystem_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_read_as_translates_at_scaled_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  first | exact @GlobalTheory.Dict.reads_isUUOver_isVtOver | exact GlobalTheory.Dict.reads_isUUOver_isVtOver | (intros; apply GlobalTheory.Dict.reads_isUUOver_isVtOver <;> assumption)
end

