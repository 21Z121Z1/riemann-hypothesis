import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardParitySignLengthOfEq
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NearerNeighbour

theorem exists_step {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Finite (M ⧸ N)] (hN : N ≠ ⊤) :
    ∃ (P : Ideal R) (x : M), P.IsMaximal ∧ x ∉ N ∧ (∀ p ∈ P, p • x ∈ N) ∧
      (Module.length R (M ⧸ (N ⊔ Submodule.span R {x}))).toNat + 1 = (Module.length R (M ⧸ N)).toNat := by
  haveI : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 hN
  haveI : IsArtinian R (M ⧸ N) := isArtinian_of_finite
  haveI : IsNoetherian R (M ⧸ N) := isNoetherian_of_finite R _
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R (M ⧸ N))
  haveI hs : IsSimpleModule R S := isSimpleModule_iff_isAtom.2 hS
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain ⟨x, hx⟩ := N.mkQ_surjective (e.symm 1 : S)
  have h0 : N.mkQ x ≠ 0 := by
    rw [hx]
    intro h
    have h1 : e.symm 1 = 0 := Subtype.ext h
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact hP.ne_top (Ideal.Quotient.zero_eq_one_iff.1 h1.symm)
  have hmap : (N ⊔ Submodule.span R {x}).map N.mkQ = S := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span, Set.image_singleton]
    refine (hS.le_iff.1 ?_).resolve_left ?_
    · rw [Submodule.span_singleton_le_iff_mem, hx]; exact (e.symm 1).2
    · rwa [Submodule.span_singleton_eq_bot]
  refine ⟨P, x, hP, fun h => h0 ((Submodule.Quotient.mk_eq_zero N).2 h), fun p hp => ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul, hx, ← Submodule.coe_smul, ← map_smul]
    have : p • (1 : R ⧸ P) = 0 := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hp
    rw [this, map_zero]; rfl
  · have h1 := Module.length_eq_add_of_exact S.subtype S.mkQ S.injective_subtype S.mkQ_surjective
      (LinearMap.exact_subtype_mkQ S)
    have h2 := (Submodule.quotientQuotientEquivQuotient N (N ⊔ Submodule.span R {x}) le_sup_left).length_eq
    rw [hmap] at h2
    have h3 : Module.length R ((M ⧸ N) ⧸ S) ≠ ⊤ := Module.length_ne_top
    rw [← h2, h1, Module.length_eq_one R S, ENat.toNat_add (by simp) h3, add_comm]
    simp

theorem exists_prime_mem {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ P := by
  have hb : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hb
  letI := Ideal.Quotient.field P
  refine ⟨ringChar (𝓞 K ⧸ P), CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_int_smul_mem {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegerScalarIntegral.main
  | exact _root_.GlobalTheory.IntegerScalarIntegral.main
  | (apply _root_.GlobalTheory.IntegerScalarIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerScalarIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerScalarIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerScalarIntegral.main ..)

theorem exists_nearer : ∀ (D : D7) (n : ℕ) (L₀ L : Lat D n), SD D L₀ → SD D L → L₀ ≠ L → ∃ (P : Ideal (𝓞 D.host.E)) (q : ℕ) (x : Fin n → D.host.E), P.IsMaximal ∧ q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ x ∈ L₀ ∧ NbD D P L x ∧ lenQ D L₀ (nbr D L x) + 1 = lenQ D L₀ L := by
  intro D n L₀ L h₀ h hne
  obtain ⟨fg₀, -, d₀⟩ := (sd_iff D L₀).1 h₀
  obtain ⟨-, sp, d⟩ := (sd_iff D L).1 h
  have hN : Submodule.comap L₀.subtype L ≠ ⊤ := by
    intro ht
    have hle : L₀ ≤ L := Submodule.comap_subtype_eq_top.1 ht
    exact hne (le_antisymm hle fun y hy => (d₀ y).2 fun x hx => (d y).1 hy x (hle hx))
  haveI : Module.Finite (𝓞 D.host.E) L₀ := Module.Finite.iff_fg.2 fg₀
  haveI : Module.Finite ℤ (L₀ ⧸ Submodule.comap L₀.subtype L) :=
    Module.Finite.trans (𝓞 D.host.E) _
  haveI : Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := Module.finite_of_fg_torsion _ fun z => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨m, hm, hy⟩ := exists_int_smul_mem L sp y.1
    refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
    change m • (Submodule.mkQ (Submodule.comap L₀.subtype L) y) = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hy
  obtain ⟨P, x, hP, hx, hPx, hlen⟩ := exists_step _ hN
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem P hP
  refine ⟨P, q, x.1, hP, hq, hqP, x.2, ⟨hx, hPx, (d₀ x.1).1 x.2 x.1 x.2⟩, ?_⟩
  have key : Submodule.comap L₀.subtype (nbr D L x.1) =
      Submodule.comap L₀.subtype L ⊔ Submodule.span (𝓞 D.host.E) {x} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
      refine Submodule.mem_sup.2 ⟨y - c • x, ?_, c • x, Submodule.mem_span_singleton.2 ⟨c, rfl⟩, sub_add_cancel _ _⟩
      have : L₀.subtype (y - c • x) = a := by
        rw [map_sub, ← hab, map_smul]; exact add_sub_cancel_right _ _
      rw [Submodule.mem_comap, this]
      exact ha.1
    · refine sup_le (fun y hy => ?_) ?_
      · exact Submodule.mem_sup_left (S := nbM D L x.1) ⟨hy, (d₀ y.1).1 y.2 x.1 x.2⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.mem_sup_right (S := nbM D L x.1) (Submodule.mem_span_singleton_self _)
  unfold lenQ
  rw [key]
  exact hlen

end GlobalTheory.NearerNeighbour
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeProperties
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.CompletedLattice

variable (D : D7)

theorem moves_one (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  rw [← h2]
  exact (h1 1).1

theorem pt_injective (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ}
    {z z' : Matrix (Fin N') (Fin N) D.host.E}
    (h : pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ z') : z = z' := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D τ (z i j) = δ * embT D τ (z' i j) := congrFun (congrFun (congrFun h τ) i) j
  exact (embT D τ).injective (mul_left_cancel₀ hδ h1)

theorem exists_mul_IhE_mem (cc : Ideal (𝓞 D.host.K)) :
    ∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  refine ⟨Ideal.absNorm D.host.𝔟, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, -, a, ha, s, hs, rfl⟩ := hy
    rw [FractionalIdeal.mem_coe] at ha
    unfold Host.AA0 at ha
    rw [FractionalIdeal.mem_inv_iff hB] at ha
    have h1 := ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.absNorm_mem D.host.𝔟))
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [map_natCast] at hr
    have h2 : inc D (r : D.host.E) ∈ OhE D := (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩
    have h3 : inc D ((c : D.host.K) : D.host.E) ∈ OhE D :=
      (AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩
    have h4 : (Ideal.absNorm D.host.𝔟 : AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) =
        inc D ((c : D.host.K) : D.host.E) * (inc D (r : D.host.E) * s) := by
      have : (r : D.host.E) = a * (Ideal.absNorm D.host.𝔟 : D.host.E) := hr
      rw [this, map_mul, map_mul, map_natCast]
      ring
    rw [h4]
    exact mul_mem h3 (mul_mem h2 hs)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem completed_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ z : Matrix (Fin N') (Fin N) D.host.E, z.map (inc D) ∈ latA D cc N N' ↔ pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ z, x = pt D (tor0 D cc δ) δ z) ∧ (∀ (ζ : XA D N N') (m : ℕ), 0 < m → ∃ z : Matrix (Fin N') (Fin N) D.host.E, ∃ a ∈ latA D cc N N', z.map (inc D) = ζ + m • a) ∧ (∀ ζ : XA D N N', ∃ m : ℕ, 0 < m ∧ m • ζ ∈ latA D cc N N') ∧ (∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D) ∧ (∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, (m : AE D) * s ∈ IhE D cc) := by
  intro D hg cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D hg cc δ hc).2.1
  have hn : 0 < Ideal.absNorm cc := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hA := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  have hB := GlobalTheory.NormSum.pt_mem_La_of_adelic D hg cc δ hcc N N' 1 1 _ _ (moves_one D N) (moves_one D N')
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hA hB
  refine ⟨fun z => ⟨fun h => hB z h, fun h => ?_⟩, fun x hx => ?_, fun ζ m hm => ?_, fun ζ => ?_,
    exists_mul_IhE_mem D cc, _, hn, GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc⟩
  · obtain ⟨z', h1, h2⟩ := hA _ h
    rw [pt_injective D cc hδ h1]
    exact h2
  · obtain ⟨z, h1, -⟩ := hA x hx
    exact ⟨z, h1⟩
  · choose e t ht h using fun (i : Fin N') (j : Fin N) => (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hcc).1 (ζ i j) m hm
    refine ⟨Matrix.of e, Matrix.of t, ht, ?_⟩
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply, Matrix.of_apply, ← h]
    ring
  · choose n hn0 h using fun k : Fin N' × Fin N => GlobalTheory.AdelicApprox.exists_denom D (ζ k.1 k.2)
    refine ⟨Ideal.absNorm cc * ∏ k, n k, Nat.mul_pos hn (Finset.prod_pos fun k _ => hn0 k), fun i j => ?_⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (i, j))
    have h1 := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D cc _ (mul_mem (natCast_mem (OhE D) c) (h (i, j)))
    rw [Matrix.smul_apply, nsmul_eq_mul, hc]
    convert h1 using 1
    push_cast
    ring

end GlobalTheory.CompletedLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeight
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory

theorem isThB_coeff_cong : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) →
    l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w →
    ∀ φ φ' : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l _ _ hl2 hlN hN hlA n w _ b _ φ φ' h h' r
  obtain ⟨f, hfinv, hfcls, hfδ, hfdl⟩ := h
  obtain ⟨f', hf'inv, hf'cls, hf'δ, hf'dl⟩ := h'
  obtain ⟨u, hu⟩ := Tower.cls_eq_pow X l n f f' (hfcls.symm.trans hf'cls)
  have hL : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hfne : (f : X.K) ≠ 0 := f.ne_zero
  have hune : (u : X.K) ≠ 0 := u.ne_zero
  have hpow : (u : X.K) ^ (l ^ n) = (f' : X.K) * (f : X.K)⁻¹ := by
    rw [hu]; field_simp
  have hinv : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) ((u : X.K) ^ (l ^ n)) := by
    intro γ hγ
    rw [hpow, map_mul, map_inv₀, hfinv γ hγ, hf'inv γ hγ]
  have hT : X.sl (ofSL ModularGroup.T) (u : X.K) = u := by
    refine TInv.sl_T_eq X N l n (Fact.out) hl2 hlN hN u hune hinv ?_
    intro δ hδ hδ'
    obtain ⟨g, hg, hfg⟩ := hfδ δ hδ hδ'
    obtain ⟨g', hg', hfg'⟩ := hf'δ δ hδ hδ'
    have hgne : g ≠ 0 := by
      rintro rfl
      rw [zero_pow hL.ne'] at hfg
      exact mul_ne_zero hfne ((map_ne_zero _).2 hfne) hfg
    refine ⟨g' * g⁻¹, ?_, ?_⟩
    · intro γ hγ
      rw [map_mul, map_inv₀, hg γ hγ, hg' γ hγ]
    · have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := (map_ne_zero _).2 hfne
      rw [mul_pow g', inv_pow, ← hfg, ← hfg', hu, map_mul, map_pow]
      field_simp
      ring
  have : Algebra.IsAlgebraic ℚ Ω := DlPow.isAlgebraic_of_tower X
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  rw [hu] at hf'dl
  exact DlPow.isDl_mul_lpow_cong X A l hlA n f u hfne hune hT φ φ' hfdl hf'dl r

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylEqEvalAtOneSmulExtremalOfRowWeightStatement
section
open GlobalTheory.DualWeyl MvPolynomial NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ), Antitone la → ∀ f ∈ nabla la K, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la → f = evalAt 1 f • extremal la K := by
  first | exact @GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | exact GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | (intros; apply GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOne
section
open GlobalTheory.DualWeyl MvPolynomial NumberField MeasureTheory
open scoped Matrix ComplexConjugate InnerProductSpace

namespace GlobalTheory.DualWeyl.Repro

variable {N : ℕ} {la : Fin N → ℕ}

theorem exists_repr (la : Fin N → ℕ) :
    ∃ k : nabla la ℂ, ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1 := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  refine ⟨(toSpace la).symm ((InnerProductSpace.toDual ℂ (Space la)).symm
    (LinearMap.toContinuousLinearMap (evSpace la 1))), fun f => ?_⟩
  rw [← inner_toSpace, LinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply]
  rfl

theorem form_rhoU_repr {k : nabla la ℂ} (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1)
    (u : UN N) (f : nabla la ℂ) :
    form la f.1 (rhoU la u⁻¹ k : Pol N ℂ) = evalAt u.1ᵀ f.1 := by
  rw [← form_rhoU u, Representation.self_inv_apply, hk, rhoU_apply, evalAt_rho, Matrix.mul_one]

theorem normSq_repr (hla : Antitone la) {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) : normSq la k.1 = 1 := by
  let e : Idx la → nabla la ℂ := fun i => (toSpace la).symm (onBasis la i)
  have he : ∀ i, toSpace la (e i) = onBasis la i := fun i => (toSpace la).apply_symm_apply _
  have h1 : ∀ g : UN N, ∑ i, ‖evalAt g.1 (e i).1‖ ^ 2 = normSq la k.1 := by
    intro g
    let u : UN N := ⟨g.1ᵀ, transpose_mem_unitaryGroup g.2⟩
    rw [← normSq_rhoU u⁻¹, ← norm_toSpace_sq, ← (onBasis la).sum_sq_norm_inner_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he, inner_toSpace, form_rhoU_repr hk]
    rfl
  have h2 : ∑ i, normSq la (e i).1 = dim la := by
    simp only [← norm_toSpace_sq, he, (onBasis la).orthonormal.1]
    simp [dim_eq_card]
  have h3 : ∑ i, normSq la (e i).1 = dim la * normSq la k.1 := by
    conv_lhs => simp only [normSq]
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ => integrable_norm_sq _]
    simp only [h1]
    simp
  have hd : (dim la : ℝ) ≠ 0 := by exact_mod_cast (dim_pos hla).ne'
  exact mul_left_cancel₀ hd (by rw [← h3, h2, mul_one])

theorem rowAct_diagonal_repr {k : nabla la ℂ}
    (hk : ∀ f : nabla la ℂ, form la f.1 k.1 = evalAt 1 f.1) (t : Fin N → ℂ) (ht : ∀ a, ‖t a‖ = 1) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) k.1 = (∏ a, t a ^ la a) • k.1 := by
  have hu : Matrix.diagonal t ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [Complex.mul_conj', ht]
  let u : UN N := ⟨_, hu⟩
  have hinv : (u⁻¹).1ᵀ = Matrix.diagonal (star t) := by
    change (star (Matrix.diagonal t))ᵀ = _
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_transpose]
  have h : rhoU la u k = (∏ a, t a ^ la a) • k := by
    apply (toSpace la).injective
    refine ext_inner_right ℂ fun v => ?_
    obtain ⟨f, rfl⟩ := (toSpace la).surjective v
    rw [inner_toSpace, inner_toSpace, ← inv_inv u, form_rhoU_repr hk, hinv, Submodule.coe_smul, form_smul_right,
      hk, ← Matrix.one_mul (Matrix.diagonal (star t)), ← evalAt_colAct,
      colAct_of_mem f.2 _ (Matrix.blockTriangular_diagonal _), map_smul]
    simp [diagChar]
  have h' := congrArg Subtype.val h
  rwa [rhoU_apply, coe_rho, Matrix.diagonal_transpose] at h'

theorem isWeightedHomogeneous_of_torus {f : Pol N ℂ}
    (h : ∀ t : Fin N → ℂ, (∀ a, ‖t a‖ = 1) →
      Formalism.GradedWeylDivisibility.rowAct ℂ (Matrix.diagonal t) f = (∏ a, t a ^ la a) • f) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la := by
  classical
  intro m hm
  funext a
  rw [Formalism.GradedWeylDivisibility.ldrow_weight_rowW]
  have hn : Formalism.GradedWeylDivisibility.rowDeg m a + la a + 1 ≠ 0 := by omega
  have hz := Complex.isPrimitiveRoot_exp _ hn
  have hz1 := hz.norm'_eq_one hn
  generalize Complex.exp _ = z at hz hz1
  have h1 := congrArg (coeff m) (h (Function.update 1 a z) fun b => by
    by_cases hb : b = a
    · subst hb; simpa using hz1
    · simp [Function.update_of_ne hb])
  rw [Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, coeff_smul, smul_eq_mul, mul_comm] at h1
  have h2 := mul_right_cancel₀ hm h1
  have h3 : ∀ d : Fin N → ℕ, ∏ b, Function.update (1 : Fin N → ℂ) a z b ^ d b = z ^ d a := by
    intro d
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  rw [h3, h3] at h2
  exact hz.pow_inj (by omega) (by omega) h2

theorem extremal_reproducing : ∀ (N : ℕ) (la : Fin N → ℕ), Antitone la →
    (∀ f ∈ nabla la ℂ, form la f (extremal la ℂ) = evalAt 1 f) ∧ normSq la (extremal la ℂ) = 1 := by
  intro N la hla
  obtain ⟨k, hk⟩ := exists_repr la
  have h1 := normSq_repr hla hk
  have h2 : evalAt 1 k.1 = 1 := by rw [← hk, form_self, h1, Complex.ofReal_one]
  have h3 := GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight ℂ N la hla k.1 k.2 (isWeightedHomogeneous_of_torus (rowAct_diagonal_repr hk))
  rw [h2, one_smul] at h3
  rw [← h3]
  exact ⟨fun f hf => hk ⟨f, hf⟩, h1⟩

end GlobalTheory.DualWeyl.Repro
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

variable {Λ : AddSubgroup ℂ}

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma sgStar_add_lattice_eq_mul_exp (hΛ : _root_.GlobalTheory.EvenTheta.IsLat Λ) {a : ℂ} (ha : a ∈ Λ)
    (z : ℂ) :
    _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ (z + a) = (if a / 2 ∈ Λ then 1 else -1) * _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ z *
      Complex.exp (↑Real.pi * z * (starRingEnd ℂ) a / ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ) +
        ↑Real.pi * a * (starRingEnd ℂ) a / (2 * ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ))) := by
  have h := hΛ.sg_law ha z
  unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h
  rw [← h, mul_assoc, ← Complex.exp_add]
  ring_nf <;> simp

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma mul_exp_eq_one_of_exp_relation {ε s x y w k : ℂ} (hs : s ≠ 0)
    (h : -1 * s * Complex.exp x = ε * (-1 * s * Complex.exp y) * Complex.exp w)
    (hk : y + w = x + k) : ε * Complex.exp k = 1 := by
  have h' : -1 * s * Complex.exp x = ε * (-1 * s * (Complex.exp x * Complex.exp k)) := by
    rw [← Complex.exp_add, ← hk, Complex.exp_add]
    linear_combination h
  have hprod : (s * Complex.exp x) * (ε * Complex.exp k - 1) = 0 := by
    linear_combination h'
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact absurd h0 (mul_ne_zero hs (Complex.exp_ne_zero x))
  · exact sub_eq_zero.1 h0

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma mul_mul_exp_eq_of_mul_exp_eq_one {ε k a s q : ℂ} (h : ε * Complex.exp k = 1) (hs : s = k + q) :
    ε * (a * Complex.exp s) = a * Complex.exp q := by
  rw [hs, Complex.exp_add]
  linear_combination (a * Complex.exp q) * h

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in

theorem _root_.GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties : ∀ Λ : AddSubgroup ℂ, _root_.GlobalTheory.EvenTheta.IsLat Λ →
    ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) ∧ _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ 0 = 1 ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ (-z) = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z ^ 2 = _root_.GlobalTheory.EvenTheta.sqTh Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧
    ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ ω (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) z = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z := by
  intro Λ hΛ t ht h2t
  have hσt : _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ t ≠ 0 := fun h => ht ((hΛ.sg_eq_zero t).1 h)
  have hhalf : ¬ (2 * t / 2 ∈ Λ) := by rwa [mul_div_cancel_left₀ t two_ne_zero]
  have hU0 : _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) 0 ≠ 0 := by
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [zero_add]
    exact mul_ne_zero hσt (Complex.exp_ne_zero _)
  have hopp : ∀ y, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ (-t) (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y = -_root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y := by
    intro y
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [show y + t = y + -t + 2 * t by ring, sgStar_add_lattice_eq_mul_exp hΛ h2t, if_neg hhalf]
    simp only [mul_assoc, ← Complex.exp_add, map_neg, map_mul, map_ofNat]
    ring_nf
  have heven : ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) (-z) = _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) z := by
    intro z
    have h := hopp z
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h ⊢
    rw [show -z + t = -(z + -t) by ring, hΛ.sg_neg]
    simp only [map_neg] at h ⊢
    ring_nf at h ⊢
    linear_combination -h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hd := hΛ.differentiable
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    fun_prop
  · unfold _root_.Formalism.MainNotions.GL3Theta.th0
    exact div_self hU0
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [heven]
  · intro z
    have h := hΛ.sqTh_mul ht z
    rw [hopp, hopp] at h
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hU0)]
    linear_combination h
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_eq_zero_iff, or_iff_left hU0]
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), hΛ.sg_eq_zero]
  · intro ω hω hωt z
    have hsum : ¬ ((ω + 2 * t) / 2 ∈ Λ) := by
      rwa [show (ω + 2 * t) / 2 = ω / 2 + t by ring]
    have h1 := sgStar_add_lattice_eq_mul_exp hΛ (add_mem hω h2t) t
    have h2 := sgStar_add_lattice_eq_mul_exp hΛ hω (t + 2 * t)
    have h3 := sgStar_add_lattice_eq_mul_exp hΛ h2t t
    rw [if_neg hsum] at h1
    rw [if_neg hhalf] at h3
    rw [show t + 2 * t + ω = t + (ω + 2 * t) by ring, h1, h3] at h2
    have hε := mul_exp_eq_one_of_exp_relation
      (k := (↑Real.pi * t * (starRingEnd ℂ) ω - ↑Real.pi * ω * (starRingEnd ℂ) t) /
        ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ)) hσt h2 (by simp only [map_add, map_mul, map_ofNat]; ring)
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    beta_reduce
    rw [show z + ω + t = z + t + ω by ring, sgStar_add_lattice_eq_mul_exp hΛ hω, div_mul_eq_mul_div]
    congr 1
    simp only [mul_assoc, ← Complex.exp_add]
    exact mul_mul_exp_eq_of_mul_exp_eq_one hε (by ring)

end GlobalTheory.EvenTheta
end

