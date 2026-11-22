import Mathlib
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardDvdSumTracePow
section
namespace GlobalTheory.MinkowskiExact

open Polynomial

theorem card_dvd_sum_trace {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) : (Fintype.card H : ℤ) ∣ ∑ g, (ρ g).trace := by
  let σ : H →* Matrix ι ι ℚ := (Int.castRingHom ℚ).mapMatrix.toMonoidHom.comp ρ
  have hc : (Fintype.card H : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : ∀ h, σ h * ∑ g, σ g = ∑ g, σ g := by
    intro h
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => (map_mul σ h g).symm
  have h2 : (∑ g, σ g) * ∑ g, σ g = (Fintype.card H : ℚ) • ∑ g, σ g := by
    rw [Finset.sum_mul, Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  let e : Matrix ι ι ℚ := (Fintype.card H : ℚ)⁻¹ • ∑ g, σ g
  have he : e * e = e := by
    simp only [e]
    rw [smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hi : IsIdempotentElem (Matrix.toLin' e) := by
    change Matrix.toLin' e ∘ₗ Matrix.toLin' e = Matrix.toLin' e
    rw [← Matrix.toLin'_mul, he]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [Matrix.trace_toLin'_eq] at ht
  refine ⟨Module.finrank ℚ (LinearMap.range (Matrix.toLin' e)), ?_⟩
  have h3 : ∀ g, (σ g).trace = ((ρ g).trace : ℚ) := by
    intro g
    simp [σ, Matrix.trace]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [← ht]
  simp only [e]
  rw [Matrix.trace_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun g _ => (h3 g).symm

theorem card_dvd_sum_trace_pow {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) (j : ℕ) : (Fintype.card H : ℤ) ∣ ∑ g, (ρ g).trace ^ j := by
  let τ : H →* Matrix (Fin j → ι) (Fin j → ι) ℤ :=
    { toFun := fun g => Matrix.of fun a b => ∏ i, ρ g (a i) (b i)
      map_one' := by
        ext a b
        simp only [map_one, Matrix.of_apply, Matrix.one_apply]
        rw [Finset.prod_ite_zero]
        simp [funext_iff]
      map_mul' := fun g h => by
        ext a b
        simp only [map_mul, Matrix.of_apply, Matrix.mul_apply]
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun c _ => Finset.prod_mul_distrib }
  have h := card_dvd_sum_trace τ
  convert h using 2 with g
  rw [Matrix.trace, Fintype.sum_pow]
  rfl

theorem card_dvd_sum_eval {H ι : Type} [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℤ) (f : ℤ[X]) : (Fintype.card H : ℤ) ∣ ∑ g, f.eval (ρ g).trace := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, Finset.sum_add_distrib]
    exact dvd_add hp hq
  | monomial j a =>
    simp only [eval_monomial, ← Finset.mul_sum]
    exact Dvd.dvd.mul_left (card_dvd_sum_trace_pow ρ j) a

theorem norm_root {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1)
    {z : ℂ} (hz : z ∈ A.charpoly.roots) : ‖z‖ = 1 := by
  have h1 : z ∈ spectrum ℂ A :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hz)
  haveI : Nontrivial (Matrix (Fin n) (Fin n) ℂ) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    rw [spectrum.of_subsingleton] at h1
    exact h1
  have h2 := spectrum.pow_mem_pow A m h1
  rw [h, spectrum.one_eq, Set.mem_singleton_iff] at h2
  exact Complex.norm_eq_one_of_pow_eq_one h2 hm

theorem card_roots {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Multiset.card A.charpoly.roots = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem norm_trace_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1) :
    ‖A.trace‖ ≤ n := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_congr rfl fun z hz => norm_root A hm h hz]
  simp [card_roots]

theorem eq_one_of_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (hm : m ≠ 0) (h : A ^ m = 1)
    (ht : A.trace = n) : A = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  rw [Matrix.trace_eq_sum_roots_charpoly] at ht
  have hre : ∀ z ∈ A.charpoly.roots, z.re ≤ 1 := fun z hz =>
    (Complex.re_le_norm z).trans (norm_root A hm h hz).le
  have hs : (A.charpoly.roots.map fun z => 1 - z.re).sum = 0 := by
    have := congrArg Complex.re ht
    rw [Multiset.sum_map_sub]
    have h2 := map_multiset_sum Complex.reAddGroupHom A.charpoly.roots
    simp only [Complex.coe_reAddGroupHom] at h2
    rw [h2] at this
    simp [card_roots, this]
  have h1 : ∀ z ∈ A.charpoly.roots, z = 1 := by
    intro z hz
    have h0 : 1 - z.re = 0 := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero (by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
      linarith [hre w hw]) hs _ (Multiset.mem_map_of_mem _ hz)
    have h3 := norm_root A hm h hz
    have h4 : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, h3]; norm_num
    have h5 : z.re = 1 := by linarith
    rw [h5] at h4
    apply Complex.ext
    · simpa using h5
    · simpa using h4
  have hch : A.charpoly = (X - C 1) ^ n := by
    rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic,
      Multiset.eq_replicate.2 ⟨card_roots A, h1⟩]
    simp
  have hsq : Squarefree (minpoly ℂ A) := by
    have hsep : (X ^ m - C 1 : ℂ[X]).Separable :=
      separable_X_pow_sub_C 1 (by exact_mod_cast hm) one_ne_zero
    refine hsep.squarefree.squarefree_of_dvd (minpoly.dvd ℂ A ?_)
    simp [h]
  have hd : minpoly ℂ A ∣ X - C 1 := by
    rw [← hsq.dvd_pow_iff_dvd hn.ne', ← hch]
    exact A.minpoly_dvd_charpoly
  have := aeval_eq_zero_of_dvd_aeval_eq_zero hd (minpoly.aeval ℂ A)
  simpa [sub_eq_zero] using this

theorem two_dvd_sub_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {k : ℕ} (h : A ^ 2 ^ k = 1) :
    (2 : ℤ) ∣ n - A.trace := by
  have key : ∀ (k : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod 2)), (B ^ 2 ^ k).trace = B.trace := by
    intro k B
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ZMod.trace_pow_card, ZMod.pow_card, ih]
  have h1 := key k ((Int.castRingHom (ZMod 2)).mapMatrix A)
  rw [← map_pow, h, map_one, Matrix.trace_one, Fintype.card_fin] at h1
  have h2 : (((n : ℤ) - A.trace : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [h1]
    simp [Matrix.trace]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h2

theorem card_two_group_dvd {H : Type} [Group H] [Fintype H] {n k : ℕ} (ρ : H →* Matrix (Fin n) (Fin n) ℤ)
    (hρ : ∀ g, ρ g = 1 → g = 1) (hk : Fintype.card H = 2 ^ k) : 2 ^ k ∣ 2 ^ n * n.factorial := by
  classical
  have h := card_dvd_sum_eval ρ (∏ i ∈ Finset.range n, (X - C ((n : ℤ) - 2 * (i + 1))))
  rw [Finset.sum_eq_single (1 : H)] at h
  · rw [hk, map_one, Matrix.trace_one, Fintype.card_fin, eval_prod] at h
    have e : ∏ i ∈ Finset.range n, eval (n : ℤ) (X - C ((n : ℤ) - 2 * (i + 1)))
        = ((2 ^ n * n.factorial : ℕ) : ℤ) := by
      rw [← Finset.prod_range_add_one_eq_factorial]
      push_cast
      rw [← Finset.card_range n, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by simp
    rw [e] at h
    exact_mod_cast h
  · intro g _ hg
    have hp : ρ g ^ 2 ^ k = 1 := by rw [← map_pow, ← hk, pow_card_eq_one, map_one]
    let A : Matrix (Fin n) (Fin n) ℂ := (Int.castRingHom ℂ).mapMatrix (ρ g)
    have hA : A ^ 2 ^ k = 1 := by simp only [A]; rw [← map_pow, hp, map_one]
    have hAt : A.trace = ((ρ g).trace : ℂ) := by simp [A, Matrix.trace]
    have h1 := norm_trace_le A (by positivity) hA
    rw [hAt, Complex.norm_intCast] at h1
    have h1' : |(ρ g).trace| ≤ n := by exact_mod_cast h1
    have h2 : (ρ g).trace ≠ n := by
      intro h2
      have h3 := eq_one_of_trace A (by positivity) hA (by rw [hAt, h2]; simp)
      apply hg
      apply hρ
      apply Matrix.map_injective (f := (Int.castRingHom ℂ : ℤ → ℂ)) Int.cast_injective
      have h4 : (ρ g).map (Int.castRingHom ℂ) = 1 := h3
      simp only [h4]
      exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
    obtain ⟨c, hc⟩ := two_dvd_sub_trace (ρ g) hp
    obtain ⟨h5, h6⟩ := abs_le.1 h1'
    rw [eval_prod]
    refine Finset.prod_eq_zero (i := (c - 1).toNat) (Finset.mem_range.2 (by omega)) ?_
    rw [eval_sub, eval_X, eval_C]
    omega
  · simp

theorem exp_eq (n p : ℕ) (hp : p.Prime) :
    n / (p - 1) + padicValNat p (n / (p - 1)).factorial = Formalism.HermitianLatticeCounting.S6.minkowskiExp n p := by
  haveI := Fact.mk hp
  have hl : Nat.log p (n / (p - 1)) < n + 1 :=
    Nat.lt_succ_of_le ((Nat.log_le_self _ _).trans (Nat.div_le_self _ _))
  rw [padicValNat_factorial hl, Formalism.HermitianLatticeCounting.S6.minkowskiExp, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), pow_zero, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.div_div_eq_div_mul, mul_comm]

open MinkowskiOrder in

theorem minkowskiBound : Formalism.HermitianLatticeCounting.S6.MinkowskiBound := by
  intro n G hG
  have hc : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hk
  haveI := Fact.mk hp
  have hle : k ≤ n / (p - 1) + padicValNat p (n / (p - 1)).factorial := by
    by_cases h2 : p = 2
    · subst h2
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hk
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card] at hK
      have h := card_two_group_dvd ((Units.coeHom _).comp (G.subtype.comp K.subtype))
        (fun g hg => Subtype.ext (Subtype.ext (Units.ext hg))) hK
      have hf := Nat.factorial_ne_zero n
      rw [padicValNat_dvd_iff_le (by positivity), padicValNat.mul (by positivity) hf,
        padicValNat.prime_pow] at h
      simpa using h
    · obtain ⟨l, hl, hpl, h⟩ := exists_prime_gen p hp h2
      have hp2 := hp.two_le
      refine le_trans ?_ (sum_odd p l hp h2 hl hpl h n)
      rw [← val_prod n p l hp hl (by omega)]
      exact (hp.pow_dvd_iff_le_factorization (Finset.prod_ne_zero_iff.mpr fun i _ =>
        Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hl.one_lt i.2))).1
        (hk.trans (card_dvd_prod n G l hl (by omega)))
  by_cases hpn : p < n + 2
  · rw [exp_eq n p hp] at hle
    refine (pow_dvd_pow p hle).trans ?_
    exact Finset.dvd_prod_of_mem (fun q => q ^ Formalism.HermitianLatticeCounting.S6.minkowskiExp n q)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 hpn, hp⟩)
  · rw [Nat.div_eq_of_lt (by omega)] at hle
    have : k = 0 := by simpa using hle
    rw [this, pow_zero]
    exact one_dvd _

end GlobalTheory.MinkowskiExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechToPosetPosetToCechSubCoboundary
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechCmp

theorem cechToPoset_posetToCech_sub_coboundary : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R]
    (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) →
      ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf (toCech s U hU hinf f) - f := by
  intro I _ X R _ s U hU hinf f hf
  have hm : ∀ {S T : NE I}, S.set ⊆ T.set → ((op S : (NE I)ᵒᵖ) ⟶ op T) :=
    fun h => (homOfLE (NE.le_iff.2 h)).op
  have hsg : ∀ T : NE I, (NE.single T.pt).set ⊆ T.set := fun T => by
    rw [NE.set_single]; exact Set.singleton_subset_iff.2 T.pt_mem
  have sub : ∀ {S T : (NE I)ᵒᵖ} (u v : S ⟶ T), u = v := fun u v =>
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  refine ⟨fun T => -f (op (NE.single T.unop.pt)) T (hm (hsg T.unop)), ?_⟩
  funext T T' φ
  have hTT : T.unop.set ⊆ T'.unop.set := NE.le_iff.1 (leOfHom φ.unop)
  have ha' : T.unop.pt ∈ T'.unop.set := hTT T.unop.pt_mem
  have hab : (NE.pair T.unop.pt T'.unop.pt).set ⊆ T'.unop.set := by
    rw [NE.set_pair]; exact Set.insert_subset ha' (Set.singleton_subset_iff.2 T'.unop.pt_mem)
  let χ : op (NE.pair T.unop.pt T'.unop.pt) ⟶ T' := hm hab
  let ψa : op (NE.single T.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt) :=
    (homOfLE (NE.pair_le_single_left T.unop.pt T'.unop.pt)).op
  let ψb : op (NE.single T'.unop.pt) ⟶ op (NE.pair T.unop.pt T'.unop.pt) :=
    (homOfLE (NE.pair_le_single_right T.unop.pt T'.unop.pt)).op
  have c1 := Z1.comp ⟨f, hf⟩ (hm (hsg T.unop)) φ
  have c2 := Z1.comp ⟨f, hf⟩ ψa χ
  have c3 := Z1.comp ⟨f, hf⟩ ψb χ
  rw [sub (hm (hsg T.unop) ≫ φ) (ψa ≫ χ)] at c1
  have e3 : (hm (hsg T'.unop) : op (NE.single T'.unop.pt) ⟶ T') = ψb ≫ χ := sub _ _
  have key : toPos s U hU hinf (toCech s U hU hinf f) T T' φ =
      mp (capF s U hU hinf) χ (f _ _ ψa) - mp (capF s U hU hinf) χ (f _ _ ψb) := by
    apply (cv s U hU hinf T').injective
    have h1 : U T.unop.pt ⊓ U T'.unop.pt ≤ cap U (NE.pair T.unop.pt T'.unop.pt) :=
      (cap_pair U _ _).ge
    have h2 : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt :=
      le_inf (cap_le U ha') (cap_le U T'.unop.pt_mem)
    rw [cv_toPos, toCech_apply, map_sub, cv_mp, cv_mp, GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT h1 h2,
      GlobalTheory.KS.rsT_rsT h1 h2]
  simp only [amitsur_d0_apply, Pi.sub_apply, map_neg, key]
  rw [e3]
  simp only at c1 c2 c3
  linear_combination -c3 + c2 - c1

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityContinuousAtZeroEqOne
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.DensOne

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * (G.map τ * x.map (starRingEnd ℂ)) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem det_ne_zero_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (mat x τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
  exact_mod_cast sgn_ne X.p0 (a : ℕ)

theorem densF_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    densF X x = fun w => ∏ τ, ∏ i : Fin r, ‖lminor (Gw X w τ) i.castSucc‖ ^ (-2 : ℤ) := by
  funext w
  unfold densF
  simp only [dmin_cpt_orth X hx]

theorem dens_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧
      ∀ τ, (mat x τ).det ≠ 0 := by
  intro E _ _ _ r X x hx
  refine ⟨?_, ?_, det_ne_zero_of_orth X hx⟩
  · rw [densF_orth X hx]
    refine tendsto_finset_prod _ fun τ _ => tendsto_finset_prod _ fun i _ => ?_
    refine ((cont_lminor X τ i.castSucc).norm.continuousAt).zpow₀ _ (Or.inl ?_)
    simp [norm_lminor_zero]
  · rw [densF_orth X hx]
    simp only [norm_lminor_zero, _root_.one_zpow, Finset.prod_const_one]

end GlobalTheory.DensOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondInjectiveGeom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem clopenCond_injective_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) := by
  intro p _ D R _ b N w0 r hw S _ s o K κ hKf hKe hκ hrep Z et hZf hZe hadd hlin hvan
  have hkill : ∀ y, ∀ c ∈ w0 ^ r, et y ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro y c hc
    rw [← hlin]
    exact hvan _ (Submodule.subset_span ⟨c, hc, y, rfl⟩)
  have h0 : et 0 = 1 := hvan 0 (Submodule.zero_mem _)
  have hE : ∀ y, GlobalTheory.LevCover.ClopenCond Z fun _ h => h ≫ et y = 1 := by
    intro y
    obtain ⟨u, hu, -⟩ := hrep Z (et y) (hkill y)
    obtain ⟨u0, hu0, -⟩ := hrep Z (et 0) (hkill 0)
    refine (GlobalTheory.LevCover.clopenCond_eq u u0).congr fun T' h => ⟨fun H => ?_, fun H => ?_⟩
    · have hk : ∀ c ∈ w0 ^ r, (h ≫ et y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
        rw [Category.assoc, hkill y c hc, MonObj.comp_one]
      refine (hrep T' (h ≫ et y) hk).unique ?_ ?_
      · rw [Category.assoc, hu]
      · rw [Category.assoc, hu0, h0, MonObj.comp_one, H]
    · rw [← hu, ← Category.assoc, H, Category.assoc, hu0, h0, MonObj.comp_one]
  have hP : ∀ y, GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Sp k ⟶ T'.left),
      (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r := by
    intro y
    by_cases hy : y ∈ wSub D w0 r
    · exact ⟨⊤, isClosed_univ, fun T' h => ⟨fun _ => by simp, fun _ _ _ _ _ _ => hy⟩⟩
    · obtain ⟨U, hU, H⟩ := hE y
      refine ⟨⟨(U : Set Z.left)ᶜ, hU.isOpen_compl⟩, U.isOpen.isClosed_compl, fun T' h =>
        ⟨fun P => ?_, fun hsub k _ _ x hx => ?_⟩⟩
      · rintro _ ⟨t, rfl⟩ ht
        obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T'.left t
        apply hy
        refine P k a ?_
        rw [← Category.assoc]
        refine (H _ _).2 ?_
        rintro _ ⟨q, rfl⟩
        have haq : a q = t := (ha ▸ Set.mem_range_self q : a q ∈ ({t} : Set T'.left))
        simp only [Over.comp_left, Over.homMk_left, Scheme.Hom.comp_apply, haq]
        exact ht
      · rw [← Category.assoc] at hx
        have hr := (H _ _).1 hx
        obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
        exact (hsub ⟨x q, rfl⟩ (hr ⟨q, by simp⟩)).elim
  haveI := D.freeLa
  haveI := D.finLa
  have hpos : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  obtain ⟨κ', _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod D.La hpos
  have hpr : ∀ c : D.La, (p ^ r) • c ∈ wSub D w0 r := by
    intro c
    refine Submodule.subset_span ⟨(p : 𝓞 D.F) ^ r, Ideal.pow_mem_pow hw.2.1 r, c, ?_⟩
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine (GlobalTheory.LevCover.ClopenCond.forall_of_finite q hP ?_).congr fun T' h => ?_
  · intro i j hij T' h Pi k _ _ x hx
    obtain ⟨c, rfl⟩ := hq i j hij
    have he : et (i + p ^ r • c) = et i := by rw [hadd, hvan _ (hpr c), _root_.mul_one]
    rw [he] at hx
    exact (wSub D w0 r).add_mem (Pi k x hx) (hpr c)
  · exact ⟨fun H y k _ _ x => H k x y, fun H k _ _ x y => H y k x⟩

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1SubstEqPull2OfIsHom
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobPull

theorem cob1_subst_eq_pull2_of_isHom_formal : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), ∀ (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (φ : Fin d → MvPowerSeries (Fin d) R), (∀ i, constantCoeff (μ i) = 0) → (∀ i, constantCoeff (ν i) = 0) → IsHom μ ν φ → ∀ f : MvPowerSeries (Fin d) R, cob1 μ (subst φ f) = pull2 φ (cob1 ν f) := by
  intro R _ d μ ν φ hμ hν hφ f
  have hp : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.const
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hu : ∀ j, constantCoeff (inL (φ j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  have hv : ∀ j, constantCoeff (inR (φ j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  obtain ⟨hL, hR, hAS, -, -, hsub, -, -⟩ :=
    SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (fun j => inL (φ j))
      (fun j => inR (φ j)) hu hv
  unfold pull2 cob1
  rw [(hAS _ _).2, (hAS _ _).2, hL, hR, hsub d ν hν f]
  have e1 : subst μ (subst φ f) = subst (fun j => at2 (ν j) (fun j => inL (φ j)) (fun j => inR (φ j))) f := by
    rw [subst_comp_subst_apply hp (hasSubst_of_constantCoeff_zero hμ)]
    congr 1
    funext j
    exact hφ.hom j
  have e2 : inL (subst φ f) = subst (fun j => inL (φ j)) f := by
    unfold inL
    rw [subst_comp_subst_apply hp hX]
  have e3 : inR (subst φ f) = subst (fun j => inR (φ j)) f := by
    unfold inR
    rw [subst_comp_subst_apply hp hY]
  rw [e1, e2, e3]

end GlobalTheory.Katz.CobPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneAdditiveFormalGroupLawXPowStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose : ∀ (R : Type) [CommRing R] (d N : ℕ) (m : Fin d), 1 ≤ N → cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N, monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i)) (N.choose i : R) := by
  first | exact @GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow | exact GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow | (intros; apply GlobalTheory.coboundaryOne_additiveFormalGroupLaw_X_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHomStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocyclePullback_iff_preimage_affineHom : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) [IsAffineHom φ], (∀ (f : C1 (OAff s)) (x : HO1 s'), Red1 h f x ↔ ∃ c : Z1 (OPre φ s'), (∀ U V (a : U ⟶ V), c.1 U V a = preα φ s s' V (f U V a)) ∧ GlobalTheory.CatCoh.H1.mk _ c = (preRes φ s').pull1 x) ∧ (∀ (v : C2 (OAff s)) (z : HO2 s'), Red2 h v z ↔ ∃ c : Z2 (OPre φ s'), (∀ U V W (a : U ⟶ V) (b : V ⟶ W), c.1 U V W a b = preα φ s s' W (v U V W a b)) ∧ GlobalTheory.CatCoh.H2.mk _ c = (preRes φ s').pull2 z) ∧ (∀ y, (preRes φ s').pull1 (pullHO1 h y) = (preCoef h).pull1 y) ∧ ∀ y, (preRes φ s').pull2 (pullHO2 h y) = (preCoef h).pull2 y := by
  first | exact @GlobalTheory.AbCoh.red_iff_pre | exact GlobalTheory.AbCoh.red_iff_pre | (intros; apply GlobalTheory.AbCoh.red_iff_pre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCoboundaryOneAdditiveEqZeroOfDegreeStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coboundaryOne_additive_eq_zero_of_degree : ∀ (R : Type) [CommRing R] (d N : ℕ) (b : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree = N → coeff α b = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → coeff γ (cob1 (addLaw R d) b) = 0 := by
  first | exact @GlobalTheory.Katz.coeff_cob1_addLaw_eq_zero_of_degree_eq | exact GlobalTheory.Katz.coeff_cob1_addLaw_eq_zero_of_degree_eq | (intros; apply GlobalTheory.Katz.coeff_cob1_addLaw_eq_zero_of_degree_eq <;> assumption)
end

