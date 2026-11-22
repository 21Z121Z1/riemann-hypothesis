import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Formalism.SharpRestriction.GrowthBounds.DataG

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisDivisibleOfKernelPowersStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_divisible_of_kernel_powers : ∀ (l : ℕ) [Fact l.Prime], ∀ s : Per.Acris0 l, (∀ n : ℕ, ∃ (u w : Per.Acris0 l), s = u + (l : Per.Acris0 l) * w ∧ (u : Per.AinfP l) ∈ Per.kerP l ^ n) → (l : Per.Acris0 l) ∣ s := by
  first | exact @GlobalTheory.MemLoc.dvd_of_forall_fil_add | exact GlobalTheory.MemLoc.dvd_of_forall_fil_add | (intros; apply GlobalTheory.MemLoc.dvd_of_forall_fil_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjectiveStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  first | exact @GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective | exact GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective | (intros; apply GlobalTheory.MemLoc.algebraMap_AinfP_BdRp_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → (∀ (n : ℕ) (y : Per.BdRp l), y ∈ Per.FilP l n ↔ aDp l (xi e) ^ n ∣ y) ∧ (∀ y : Per.BdRp l, aDp l (xi e) * y = 0 → y = 0) ∧ IsAdicComplete (Ideal.span {aDp l (xi e)}) (Per.BdRp l) ∧ (∀ n : ℕ, Function.Surjective (Per.ev l n)) := by
  first | exact @GlobalTheory.MemLoc.filtration_eq_xi_pow | exact GlobalTheory.MemLoc.filtration_eq_xi_pow | (intros; apply GlobalTheory.MemLoc.filtration_eq_xi_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem invariants_finExt : ∀ (l : ℕ) [Fact l.Prime], ∀ (K : FinExt l) (x : ℂ_[l]), (∀ g ∈ GK K, Per.σC g x = x) → ∃ y ∈ K.1, ((y : Om l) : ℂ_[l]) = x := by
  intro l _ K x hx
  have h := GlobalTheory.T.ax_sen_tate_complex_padic_fixed_closure l (GK K) x hx
  have hset : {y : Om l | ∀ g ∈ GK K, g y = y} = (K.1 : Set (Om l)) := by
    ext y
    have h1 := InfiniteGalois.fixedField_fixingSubgroup K.1
    constructor
    · intro hy
      have : y ∈ IntermediateField.fixedField K.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        exact hy
      rwa [h1] at this
    · intro hy g hg
      exact (IntermediateField.mem_fixingSubgroup_iff K.1 g).1 hg y hy
  rw [hset] at h
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] K.1.toSubalgebra.toSubmodule := K.2
  have hc : IsComplete (K.1 : Set (Om l)) :=
    Submodule.complete_of_finiteDimensional (𝕜 := ℚ_[l]) K.1.toSubalgebra.toSubmodule
  have hc2 : IsComplete ((fun y : Om l => (y : ℂ_[l])) '' (K.1 : Set (Om l))) :=
    (isComplete_image_iff (UniformSpace.Completion.isUniformInducing_coe (Om l))).2 hc
  rw [hc2.isClosed.closure_eq] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, hy, rfl⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisUnique

variable {l : ℕ} [Fact l.Prime]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, e, h0, -, h1, h⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨e, ?_, fun h' => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · have := h 1
    have h2 : rootT e 1 = 1 := h'
    rw [h2] at this
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← this]
    rfl

theorem dvd_of_pow_mul {R : Type} [CommRing R] (x p : R) (h : ∀ a, x ∣ p * a → x ∣ a) (k : ℕ) (a : R)
    (ha : x ∣ p ^ k * a) : x ∣ a := by
  induction k with
  | zero => simpa using ha
  | succ k ih => exact ih (h _ (by rwa [pow_succ', mul_assoc] at ha))

theorem localization_quotient_separated_dvd {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (x p : R) [IsLocalization.Away p S]
    (h : ∀ a, x ∣ p * a → x ∣ a)
    (hc : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {x}) p}) (R ⧸ Ideal.span {x}))
    (q : S) (hq : ∀ r : ℕ, ∃ a : R, algebraMap R S x ∣ q - algebraMap R S (p ^ r * a)) :
    algebraMap R S x ∣ q := by
  have sat : ∀ b : R, algebraMap R S x ∣ algebraMap R S b → x ∣ b := by
    rintro b ⟨c, hc⟩
    obtain ⟨⟨c', ⟨_, m, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers p) c
    have e : algebraMap R S (p ^ m * b) = algebraMap R S (x * c') := by
      rw [map_mul, map_mul, hc, ← hm]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers p) S).1 e
    refine dvd_of_pow_mul x p h m _ (dvd_of_pow_mul x p h k _ ⟨p ^ k * c', ?_⟩)
    simp only at hk
    rw [hk]; ring
  obtain ⟨a0, h0⟩ := hq 0
  rw [pow_zero, one_mul] at h0
  have h1 : Ideal.Quotient.mk (Ideal.span {x}) a0 = 0 := by
    refine hc.haus _ fun r => ?_
    obtain ⟨a, ha⟩ := hq r
    have h2 : x ∣ a0 - p ^ r * a := sat _ (by
      have := dvd_sub ha h0
      rw [map_sub]
      convert this using 1
      ring)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h2
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
  have := dvd_add h0 (map_dvd (algebraMap R S) h1)
  simpa using this

theorem sep (n : ℕ) (q : Per.AinfP l ⧸ Per.kerP l ^ n)
    (hq : ∀ r : ℕ, ∃ a : Per.Ainf l, q = (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ r *
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a)) : q = 0 := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨h1, h2⟩ := GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n
  have hk : ∀ y : Per.AinfP l, y ∈ Per.kerP l ^ n ↔ algebraMap (Per.Ainf l) (Per.AinfP l) (xi e ^ n) ∣ y := by
    intro y
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_pow]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.eq_zero_iff_mem, hk]
  refine localization_quotient_separated_dvd (xi e ^ n) (l : Per.Ainf l) h1 ?_ y fun r => ?_
  · rw [map_natCast]
    exact h2.toIsHausdorff
  · obtain ⟨a, ha⟩ := hq r
    refine ⟨a, ?_⟩
    rw [← hk, ← Ideal.Quotient.eq, ha, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

theorem ev_alg (n : ℕ) (y : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) y) = Ideal.Quotient.mk _ y :=
  GlobalTheory.RingIface.ev_alg l n y

theorem ev_aDp (n : ℕ) (a : Per.Ainf l) :
    Per.ev l n (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) :=
  ev_alg n _

theorem ev_ext {x y : Per.BdRp l} (h : ∀ n, Per.ev l n x = Per.ev l n y) : x = y :=
  GlobalTheory.RingIface.ev_ext l x y h

theorem σDp_alg (g : Per.Gq l) (y : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) y) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) y) :=
  GlobalTheory.RingIface.sigDp_alg l g y

private theorem ker_evalₐ_fg {A : Type} [CommRing A] (J : Ideal A) (fg : J.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ J n) = (J ^ n).map (algebraMap A (AdicCompletion J A)) := by
  ext a
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
  have hle : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by intro x hx; simpa using hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ J a hle]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A n a)
    rw [← hb] at h ⊢
    have : b ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
  · intro h; rw [h, map_zero]

private theorem mem_map_of_ev (n : ℕ) (w : Per.BdRp l) (h : Per.ev l n w = 0) :
    w ∈ (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨ε, hε⟩ := exists_isEps l
  have fg : (Per.kerP l).FG := by
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l ε hε]
    exact Submodule.fg_span_singleton _
  obtain ⟨e, he, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have h1 : e w ∈ RingHom.ker (AdicCompletion.evalₐ (Per.kerP l) n) := by
    rw [RingHom.mem_ker, hev, h]
  rw [ker_evalₐ_fg _ fg] at h1
  have h2 : (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))) ≤
      ((Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l))).comap e.symm.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, ← he a]
    have := Ideal.mem_map_of_mem (algebraMap (Per.AinfP l) (Per.BdRp l)) ha
    simpa using this
  have h3 := h2 h1
  rw [Ideal.mem_comap] at h3
  simpa using h3

theorem ev_σDp (g : Per.Gq l) (n : ℕ) (w : Per.BdRp l) (y : Per.AinfP l)
    (h : Per.ev l n w = Ideal.Quotient.mk _ y) :
    Per.ev l n (Per.σDp g w) = Ideal.Quotient.mk _ (Per.extP (Per.σA g) y) := by
  have h0 : Per.ev l n (w - algebraMap (Per.AinfP l) (Per.BdRp l) y) = 0 := by
    rw [map_sub, h, ev_alg, sub_self]
  have h1 := mem_map_of_ev n _ h0
  have h2 : (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l)) ≤
      (RingHom.ker (Per.ev l n)).comap (Per.σDp g) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, σDp_alg, ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    exact ((Ideal.pow_right_mono (GlobalTheory.RingBasics.ker_σ g) n).trans (Ideal.le_comap_pow _ n)) ha
  have h3 := h2 h1
  rw [Ideal.mem_comap, RingHom.mem_ker, map_sub, map_sub, σDp_alg, ev_alg, sub_eq_zero] at h3
  exact h3

theorem sigA_alg (g : Per.Gq l) (s : Per.Acris0 l) :
    sigA g (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      algebraMap (Per.Acris0 l) (Per.Acris l) ⟨Per.extP (Per.σA g) s, (GlobalTheory.CrisMaps.sigA_extends g).mem _ s.2⟩ :=
  (GlobalTheory.CrisMaps.sigA_extends g).env s

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem ev_eq {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l),
      x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧
      Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) =
        Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) : Per.ev l n (j x) = Per.ev l n y := by
  obtain ⟨N, hN⟩ := hj.bdd n
  have hu : IsUnit ((l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ N) := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map (Ideal.Quotient.mk (Per.kerP l ^ n))
    rw [map_natCast] at this
    exact this.pow N
  rw [← sub_eq_zero, ← hu.mul_right_eq_zero]
  refine sep n _ fun r => ?_
  obtain ⟨s, z, a, hx, hy⟩ := h r
  obtain ⟨b, hb⟩ := hN z
  refine ⟨b - (l : Per.Ainf l) ^ N * a, ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, ev_aDp] at hy
  rw [map_mul, map_pow, map_natCast] at hb
  simp only [hx, map_add, map_sub, map_mul, map_pow, map_natCast, hj.on0]
  linear_combination (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ r * hb -
    (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ N * hy

theorem unique {j j' : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (hj' : IsCrisP j') : j' = j := by
  refine RingHom.ext fun x => ev_ext fun n => (ev_eq hj n x _ fun r => ?_).symm
  obtain ⟨N, hN⟩ := hj'.bdd n
  obtain ⟨s, z, hx⟩ := (acris_basic l).2.2.1 x (r + N)
  obtain ⟨a, ha⟩ := hN z
  refine ⟨s, (l : Per.Acris l) ^ N * z, a, by rw [hx, pow_add, mul_assoc], ?_⟩
  rw [map_mul (Per.ev l n), ev_aDp, ← ha, ← map_mul, hx, map_add, map_mul j', map_pow j', map_natCast, hj'.on0,
    add_sub_cancel_left, pow_add, mul_assoc]

theorem equivariant {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (g : Per.Gq l) (x : Per.Acris l) :
    j (sigA g x) = Per.σDp g (j x) := by
  refine ev_ext fun n => ev_eq hj n _ _ fun r => ?_
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, hx⟩ := (acris_basic l).2.2.1 x (r + N)
  obtain ⟨a, ha⟩ := hN z
  refine ⟨⟨Per.extP (Per.σA g) s, (GlobalTheory.CrisMaps.sigA_extends g).mem _ s.2⟩, (l : Per.Acris l) ^ N * sigA g z, Per.σA g a, ?_, ?_⟩
  · rw [hx, map_add, sigA_alg, map_mul, map_pow, map_natCast, pow_add, mul_assoc]
  · have hb := ev_σDp g n _ _ ha
    rw [GlobalTheory.RingBasics.awayMap_algebraMap₂, map_mul (Per.σDp g), map_pow (Per.σDp g), map_natCast] at hb
    rw [map_mul (Per.ev l n), ev_aDp, ← hb, ← map_mul, hx, map_add j, map_mul j, map_pow j, map_natCast j, hj.on0,
      map_add (Per.σDp g), σDp_alg, add_sub_cancel_left, map_mul (Per.σDp g), map_pow (Per.σDp g),
      map_natCast (Per.σDp g), pow_add, mul_assoc]

end GlobalTheory.MemLoc.CrisUnique

namespace GlobalTheory.MemLoc

theorem crisP_unique_equivariant : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → (∀ j' : Per.Acris l →+* Per.BdRp l, IsCrisP j' → j' = j) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), j (sigA g x) = Per.σDp g (j x)) ∧ ∀ (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l), (∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧ Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) = Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) → Per.ev l n (j x) = Per.ev l n y :=
  fun _ _ _ hj => ⟨fun _ hj' => CrisUnique.unique hj hj', CrisUnique.equivariant hj, CrisUnique.ev_eq hj⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralGroupAlgebraOpPreservesIntegralLevelFormsStatement
section
open NumberField
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralGroupAlgebraOp_preserves_integralLevelForms : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : NumberField.InfinitePlace K), Formalism.DivisionValues.IsConjAt v0 →
    ∀ (S : Formalism.L2.DIV.CSD K), (S.H.map v0.embedding).PosDef →
    ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r →
    ∀ (P : Subgroup G) (ψ : P →* Kˣ) (a : MonoidAlgebra K G), (∀ b, a * b = b * a) → (∀ t : G, ∃ n : ℤ, a.coeff t = n) →
    ∀ x ∈ S.lvlNab r P ψ, (S.lvlOp r P ψ a).mulVec x ∈ S.lvlNab r P ψ := by
  first | exact @GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab | exact GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab | (intros; apply GlobalTheory.CentralLevelOp.lvlOp_mem_lvlNab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtensionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (i : ℤ) (x : ℂ_[l]), i ≠ 0 → (∀ g ∈ GK K, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((C.χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) → x = 0 := by
  first | exact @GlobalTheory.MemLoc.tate_twist_invariants | exact GlobalTheory.MemLoc.tate_twist_invariants | (intros; apply GlobalTheory.MemLoc.tate_twist_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRepsSurjective
section
open MvPolynomial Formalism.MainNotions.G Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.ClassRank

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

theorem gPos_mul (v : Fin P.nV) (s : Fin (P.n' v)) (A B : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    P.gPos v s (A * B) = P.gPos v s A * P.gPos v s B := by
  ext a b
  simp only [Places.gPos, Matrix.mul_apply, map_sum, map_mul]

theorem gPos_one (v : Fin P.nV) (s : Fin (P.n' v)) : P.gPos v s 1 = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Places.gPos, Matrix.one_apply, h]

theorem subst_comp (G H : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) :
    (P.subst G).comp (P.subst H) = P.subst fun v s => H v s * G v s := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [Places.subst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem subst_one : (P.subst fun _ _ => 1) = AlgHom.id Kf _ := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [Places.subst, aeval_X, AlgHom.id_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single x.2.2.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem natAct_mul (A B : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) (F : P.Xsp) :
    P.natAct (fun v => A v * B v) F = P.natAct A (P.natAct B F) := by
  have h := congrArg (fun φ => φ F) (subst_comp (P := P)
    (fun v s => P.gPos v s ((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)))
    (fun v s => P.gPos v s ((B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))))
  simp only [AlgHom.comp_apply] at h
  simp only [Places.natAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, h,
    mul_inv_rev, Units.val_mul, gPos_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  first | rfl | (congr 1; exact mul_comm _ _)

theorem natAct_one (F : P.Xsp) : P.natAct (fun _ => 1) F = F := by
  simp only [Places.natAct, inv_one, Units.val_one, gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one,
    one_smul, subst_one, AlgHom.toLinearMap_apply, AlgHom.id_apply]

variable (C : Level P)

theorem actX_mul (γ δ : C.Γ) (F : P.Xsp) : C.actX (γ * δ) F = C.actX γ (C.actX δ F) := by
  simp only [Level.actX, map_mul]
  exact natAct_mul _ _ F

theorem actX_one (F : P.Xsp) : C.actX 1 F = F := by
  simp only [Level.actX, map_one]
  exact natAct_one F

theorem smul_mul (γ δ : C.Γ) (L : P.Tup) : C.smul (γ * δ) L = C.smul γ (C.smul δ L) := by
  funext v
  simp only [Level.smul, map_mul, Units.val_mul, Matrix.mulVecLin_mul, ← Submodule.map_comp]
  rfl

theorem smul_one (L : P.Tup) : C.smul 1 L = L := by
  funext v
  simp only [Level.smul, map_one, Units.val_one, Matrix.mulVecLin_one]
  exact Submodule.map_id _

theorem isLatTup_smul (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) := by
  intro v
  obtain ⟨g, hg, e⟩ := hL v
  refine ⟨(C.act v γ : Matrix _ _ _) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (C.act v γ).isUnit).mul hg
  · simp only [Level.smul, e, colSpan, Submodule.map_span, ← Set.range_comp]
    congr 2

theorem isLatTup_smul_iff (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := by
  refine ⟨fun h => ?_, isLatTup_smul C γ⟩
  have := isLatTup_smul C γ⁻¹ h
  rwa [← smul_mul, inv_mul_cancel, smul_one] at this

theorem mem_funMod_iff (Hv : P.Tup → Submodule O P.Xsp) (F : P.Tup → P.Xsp) :
    F ∈ C.funMod Hv ↔ (∀ L, P.IsLatTup L → F L ∈ Hv L) ∧ (∀ L, ¬ P.IsLatTup L → F L = 0) ∧
      ∀ γ L, F (C.smul γ L) = (C.χ γ : O) • C.actX γ (F L) := by
  simp only [Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, sub_eq_zero, and_assoc,
    LinearMap.restrictScalars_apply]

structure IsReps {ι : Type} (rep : ι → P.Tup) : Prop where
  lat : ∀ i, P.IsLatTup (rep i)
  surj : ∀ L, P.IsLatTup L → ∃ i γ, L = C.smul γ (rep i)
  inj : ∀ i j γ, C.smul γ (rep i) = rep j → i = j

def evalReps (Hv : P.Tup → Submodule O P.Xsp) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    C.funMod Hv →ₗ[O] ∀ i, Hv (rep i) where
  toFun F i := ⟨F.1 (rep i), ((mem_funMod_iff C Hv F.1).1 F.2).1 _ (hr.lat i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalReps_injective (Hv : P.Tup → Submodule O P.Xsp) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    Function.Injective (evalReps C Hv hr) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  obtain ⟨-, h0, hγ⟩ := (mem_funMod_iff C Hv F.1).1 F.2
  apply Subtype.ext
  funext L
  by_cases hL : P.IsLatTup L
  · obtain ⟨i, γ, rfl⟩ := hr.surj L hL
    have : F.1 (rep i) = 0 := congrArg Subtype.val (congrFun hF i)
    rw [hγ, this, map_zero, smul_zero]
    rfl
  · exact h0 L hL

theorem evalReps_surjective (Hv : P.Tup → Submodule O P.Xsp)
    (hact : ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
      (Hv L).map ((C.actX γ).restrictScalars O) = Hv (C.smul γ L))
    (htriv : C.TrivStab) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    Function.Surjective (evalReps C Hv hr) := by
  classical
  intro x
  choose idx gam hgam using hr.surj
  let F : P.Tup → P.Xsp := fun L =>
    if h : P.IsLatTup L then (C.χ (gam L h) : O) • C.actX (gam L h) (x (idx L h) : P.Xsp) else 0
  have key : ∀ i γ, F (C.smul γ (rep i)) = (C.χ γ : O) • C.actX γ (x i : P.Xsp) := by
    intro i γ
    have h := isLatTup_smul C γ (hr.lat i)
    have e := hgam _ h
    simp only [F, dif_pos h]
    generalize idx _ h = j at e ⊢
    generalize gam _ h = δ at e ⊢
    have e' : C.smul (δ⁻¹ * γ) (rep i) = rep j := by
      rw [smul_mul, e, ← smul_mul, inv_mul_cancel, smul_one]
    obtain rfl := hr.inj _ _ _ e'
    obtain rfl : δ = γ := inv_mul_eq_one.1 (htriv _ _ (hr.lat i) e')
    rfl
  refine ⟨⟨F, (mem_funMod_iff C Hv F).2 ⟨fun L hL => ?_, fun L hL => dif_neg hL, fun γ L => ?_⟩⟩, ?_⟩
  · obtain ⟨i, γ, rfl⟩ := hr.surj L hL
    rw [key, ← hact γ _ (hr.lat i)]
    exact Submodule.smul_mem _ _ ⟨_, (x i).2, rfl⟩
  · by_cases hL : P.IsLatTup L
    · obtain ⟨i, δ, rfl⟩ := hr.surj L hL
      rw [← smul_mul, key, key, map_mul, Units.val_mul, mul_smul, actX_mul]
      congr 1
      exact (((C.actX γ).restrictScalars O).map_smul _ _).symm
    · have h1 : F L = 0 := dif_neg hL
      have h2 : F (C.smul γ L) = 0 := dif_neg (fun h => hL ((isLatTup_smul_iff C γ L).1 h))
      rw [h1, h2, map_zero, smul_zero]
  · funext i
    apply Subtype.ext
    have := key i 1
    rw [smul_one, map_one, Units.val_one, one_smul, actX_one] at this
    exact this

def evalRepsEquiv (Hv : P.Tup → Submodule O P.Xsp)
    (hact : ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
      (Hv L).map ((C.actX γ).restrictScalars O) = Hv (C.smul γ L))
    (htriv : C.TrivStab) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    C.funMod Hv ≃ₗ[O] ∀ i, Hv (rep i) :=
  LinearEquiv.ofBijective (evalReps C Hv hr) ⟨evalReps_injective C Hv hr, evalReps_surjective C Hv hact htriv hr⟩

theorem d_eq_card_mul (G : GAtP p) (hinj : Function.Injective (algebraMap G.O G.Kf)) (htriv : G.TrivStab)
    (hact : ∀ c, (G.lev c).ActHW) {ι : G.comp → Type} [∀ c, Fintype (ι c)] (rep : ∀ c, ι c → G.P.Tup)
    (hr : ∀ c, IsReps (G.lev c) (rep c)) (hfg : ∀ c i, (G.P.HtupW (rep c i)).FG) (n : ℕ)
    (hn : ∀ c i, Module.finrank G.O (G.P.HtupW (rep c i)) = n) :
    G.d = (∑ c, Fintype.card (ι c)) * n := by
  have : FaithfulSMul G.O G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.IsTorsionFree G.O G.P.Xsp := Module.IsTorsionFree.trans G.Kf
  have : ∀ c i, Module.Finite G.O (G.P.HtupW (rep c i)) := fun c i => Module.Finite.iff_fg.2 (hfg c i)
  have : ∀ c i, Module.Free G.O (G.P.HtupW (rep c i)) := fun c i => inferInstance
  let e0 : G.M ≃ₗ[G.O] ∀ c, (G.lev c).funMod G.P.HtupW :=
    { toFun := fun F c => ⟨F.1 c, F.2 c (Set.mem_univ c)⟩
      invFun := fun F => ⟨fun c => (F c).1, fun c _ => (F c).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 := e0.trans (LinearEquiv.piCongrRight fun c =>
    evalRepsEquiv (G.lev c) G.P.HtupW (hact c) (htriv c) (hr c))
  rw [GAtP.d, e1.finrank_eq, Module.finrank_pi_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Module.finrank_pi_fintype]
  simp [hn]

end GlobalTheory.ClassRank
end
end

