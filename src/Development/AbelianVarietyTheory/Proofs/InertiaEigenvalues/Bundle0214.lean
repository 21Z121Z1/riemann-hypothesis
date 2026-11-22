import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicMonodromyPolynomialsRaiseDegree
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.DegreeRaise
open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds

theorem mem_degrees {e : ℕ} {Sig : Finset (ZMod e)} {c : ZMod e} {m m' i : ℕ} :
    i ∈ degrees Sig c m m' ↔ ∃ c' ∈ Sig, ∃ n, (m ≤ n ∧ n < m') ∧ (c - c').val + n * e = i := by
  simp only [degrees, Finset.mem_image, Finset.mem_product, Finset.mem_Ico, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

theorem bounds_of_mem {e : ℕ} [NeZero e] {Sig : Finset (ZMod e)} {c : ZMod e} {m m' i : ℕ}
    (h : i ∈ degrees Sig c m m') : m * e ≤ i ∧ i < m' * e := by
  obtain ⟨c', -, n, ⟨h1, h2⟩, rfl⟩ := mem_degrees.1 h
  have := ZMod.val_lt (c - c')
  constructor <;> nlinarith

theorem rootPoly_monic (T : Finset ℕ) : (rootPoly T).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem mem_roots_rootPoly {T : Finset ℕ} {x : ℤ} (h : x ∈ (rootPoly T).roots) : ∃ i ∈ T, x = i := by
  rw [Polynomial.mem_roots (rootPoly_monic T).ne_zero, Polynomial.IsRoot, rootPoly, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff] at h
  obtain ⟨i, hi, h⟩ := h
  exact ⟨i, hi, by simpa [sub_eq_zero] using h⟩

theorem card_degrees_le {e : ℕ} (Sig : Finset (ZMod e)) (c : ZMod e) (m m' : ℕ) :
    (degrees Sig c m m').card ≤ Sig.card * (m' - m) :=
  Finset.card_image_le.trans (by simp [Finset.card_product])

theorem degreeBounds {e : ℕ} [NeZero e] (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ) :
    DegreeBounds Sig c A' where
  lt_of_mem₁ i hi := by have := bounds_of_mem hi; nlinarith
  mem_Ico₂ j hj := by have := bounds_of_mem hj; constructor <;> nlinarith
  monic₁ := rootPoly_monic _
  monic₂ := rootPoly_monic _
  disjoint_roots := by
    rw [Multiset.disjoint_left]
    intro x h1 h2
    obtain ⟨i, hi, rfl⟩ := mem_roots_rootPoly h1
    obtain ⟨j, hj, hij⟩ := mem_roots_rootPoly h2
    have := bounds_of_mem hi
    have := bounds_of_mem hj
    have : i = j := by exact_mod_cast hij
    omega
  card₁ := (card_degrees_le _ _ _ _).trans (by simp)
  card₂ := (card_degrees_le _ _ _ _).trans (by rw [show 2 * A' - A' = A' by omega])

theorem climb {R S V : Type} [Ring R] [Ring S] [AddCommGroup V] [Module R V] [Module S V]
    (f : Module.End S V) (W : ℕ → Submodule R V) (m : ℕ) :
    ∀ k (T : Finset ℕ), (∀ i ∈ T, ∀ x ∈ W i, f x - i • x ∈ W (i + 1)) →
      (∀ i, m ≤ i → i < m + k → i ∉ T → W i ≤ W (i + 1)) → T ⊆ Finset.Ico m (m + k) →
      ∀ x ∈ W m, Polynomial.aeval f (rootPoly T) x ∈ W (m + k) := by
  intro k
  induction k with
  | zero =>
    intro T _ _ hT x hx
    have : T = ∅ := Finset.subset_empty.1 (by simpa using hT)
    subst this
    simpa [rootPoly] using hx
  | succ k ih =>
    intro T hstep hskip hT x hx
    by_cases hj : m + k ∈ T
    · have hT' : T.erase (m + k) ⊆ Finset.Ico m (m + k) := fun i hi => by
        have h1 := Finset.mem_erase.1 hi
        have h2 := Finset.mem_Ico.1 (hT h1.2)
        exact Finset.mem_Ico.2 ⟨h2.1, by omega⟩
      have hy := ih (T.erase (m + k)) (fun i hi => hstep i (Finset.mem_of_mem_erase hi))
        (fun i h1 h2 h3 => hskip i h1 (by omega) fun h => h3 (Finset.mem_erase.2 ⟨by omega, h⟩)) hT' x hx
      have hP : rootPoly T = (Polynomial.X - Polynomial.C ((m + k : ℕ) : ℤ)) * rootPoly (T.erase (m + k)) :=
        (Finset.mul_prod_erase T _ hj).symm
      rw [hP, map_mul, Module.End.mul_apply]
      have := hstep _ hj _ hy
      rw [← add_assoc]
      convert this using 1
      simp [Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_add_neg]
      rw [add_smul]
      abel
    · have hT' : T ⊆ Finset.Ico m (m + k) := fun i hi => by
        have h2 := Finset.mem_Ico.1 (hT hi)
        refine Finset.mem_Ico.2 ⟨h2.1, ?_⟩
        rcases Nat.lt_or_ge i (m + k) with h | h
        · exact h
        · exact absurd (show i = m + k by omega ▸ hi) hj
      exact hskip (m + k) (by omega) (by omega) hj
        (ih T hstep (fun i h1 h2 h3 => hskip i h1 (by omega) h3) hT' x hx)

section Main

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a] {ι : Type} [Fintype ι] [DecidableEq ι] {η H : ℕ}

theorem actD_red (D : BKDat O K l e a ι η H) (c : ZMod e) (i : ℕ) (y : Vec K a ι)
    (hx : (X : K⟦X⟧) ^ i • y ∈ D.desc.isotypic c) (ζ : rootsOfUnity e K) (τ : ZMod a) :
    D.desc.actD (TameGal.inertia ζ) (red y) τ =
      (TameGal.inertia ζ : TameGal K l e a).root τ ^ (c - (i : ZMod e)).val • red y τ := by
  have h1 := hx ζ τ
  have h2 : D.desc.act (TameGal.inertia ζ) ((X : K⟦X⟧) ^ i • y) =
      ringAct (TameGal.inertia ζ) ((fun _ => X) ^ i) • D.desc.act (TameGal.inertia ζ) y :=
    D.desc.act_smul_tot _ _ y
  rw [map_pow, ringAct_X] at h2
  rw [h2] at h1
  have hr0 := (TameGal.inertia ζ : TameGal K l e a).root_ne_zero τ
  have hre := (TameGal.inertia ζ : TameGal K l e a).root_pow τ
  have hmod : ((c - (i : ZMod e)).val + i) % e = c.val := by
    rw [← ZMod.val_natCast, Nat.cast_add, ZMod.natCast_zmod_val, sub_add_cancel]
  ext j
  have h3 := congrFun h1 j
  simp only [Pi.smul_apply', Pi.pow_apply, Pi.smul_apply, smul_eq_mul] at h3
  rw [← D.desc.red_act]
  simp only [red_apply, powerSeriesVecReduceModU_apply, Pi.smul_apply, smul_eq_mul]
  generalize (TameGal.inertia ζ : TameGal K l e a).root τ = r at h3 hr0 hre ⊢
  have hpow (n : ℕ) : r ^ n = r ^ (n % e) := by
    conv_lhs => rw [← Nat.mod_add_div n e, pow_add, pow_mul, hre, one_pow, mul_one]
  have hc : r ^ c.val = r ^ (c - (i : ZMod e)).val * r ^ i := by
    rw [← pow_add, hpow ((c - (i : ZMod e)).val + i), hmod]
  have h4 : (X : K⟦X⟧) ^ i * (C (r ^ i) * D.desc.act (TameGal.inertia ζ) y τ j) =
      X ^ i * (C (r ^ c.val) * y τ j) := by
    rw [smul_eq_C_mul, mul_pow, ← map_pow] at h3
    linear_combination h3
  have h5 := congrArg constantCoeff (mul_left_cancel₀ (pow_ne_zero i PowerSeries.X_ne_zero) h4)
  simp only [map_mul, constantCoeff_C] at h5
  apply mul_left_cancel₀ (pow_ne_zero i hr0)
  rw [h5, hc]
  ring

theorem vL_eq (P : PhiMod O K l e a ι) (n : ℕ) : vL P n = uL P (e * n) := by
  show mulL P ((X ^ e) ^ n) = mulL P (X ^ (e * n))
  rw [pow_mul]

theorem graded (D : BKDat O K l e a ι η H) (Sig : Finset (ZMod e))
    (hch : ∀ τ, D.desc.chars τ ⊆ (Sig : Set (ZMod e))) (c : ZMod e) (i : ℕ)
    (hi : ¬ ∃ c' ∈ Sig, ∃ n : ℕ, i = (c - c').val + n * e) :
    part (D.desc.isotypic c) (uL D.toPhiMod i) ≤ uL D.toPhiMod (i + 1) := by
  intro x hx
  obtain ⟨hxL, hxW⟩ := Submodule.mem_inf.1 hx
  obtain ⟨y, hy, rfl⟩ := mem_mulL.1 hxL
  have hred : red y = 0 := by
    by_contra hne
    obtain ⟨τ, hτ⟩ : ∃ τ, red y τ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hmem : c - (i : ZMod e) ∈ D.desc.chars τ := ⟨red y, hτ, fun ζ => actD_red D c i y hxW ζ τ⟩
    refine hi ⟨_, hch τ hmem, i / e, ?_⟩
    rw [sub_sub_cancel, ZMod.val_natCast]
    exact (Nat.mod_add_div' i e).symm
  have hw : ∀ τ, ∃ w ∈ D.toPhiMod.Lcomp τ, y τ = (X : K⟦X⟧) • w := by
    intro τ
    have hyτ : y τ ∈ D.toPhiMod.Lcomp τ := mem_tot.1 hy τ
    have h0 : (⟨y τ, hyτ⟩ : D.toPhiMod.Lcomp τ) ∈ D.toPhiMod.uL τ :=
      D.toPhiMod.mem_uL_iff.2 (by simpa using congrFun hred τ)
    rw [PhiMod.uL, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h0
    obtain ⟨w, -, hw⟩ := h0
    refine ⟨w, w.2, ?_⟩
    rw [show y τ = ((⟨y τ, hyτ⟩ : D.toPhiMod.Lcomp τ) : ι → K⟦X⟧) from rfl, ← hw, Submodule.coe_smul,
      Subalgebra.smul_def, coe_uIn]
  choose w hwL hwy using hw
  have hy' : y = (X : K⟦X⟧) • (fun τ => w τ) := funext hwy
  refine mem_mulL.2 ⟨fun τ => w τ, mem_tot.2 hwL, ?_⟩
  rw [hy', pow_succ, mul_smul]

theorem step {P : PhiMod O K l e a ι} {W : Submodule K (Vec K a ι)} (hM : ModHigh P W) (i : ℕ)
    (hi : i < l * e) (x : Vec K a ι) (hx : x ∈ part W (uL P i) ⊔ part W (MMHigh P)) :
    P.conn x - i • x ∈ part W (uL P (i + 1)) ⊔ part W (MMHigh P) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  have h1 := hM.conn_graded i hi y hy
  have h2 : P.conn z - i • z ∈ part W (MMHigh P) :=
    sub_mem (hM.conn_high z hz) (Submodule.smul_of_tower_mem _ i hz)
  have : P.conn (y + z) - i • (y + z) = (P.conn y - i • y) + (P.conn z - i • z) := by
    rw [map_add, smul_add]
    abel
  rw [this]
  exact add_mem h1 (Submodule.mem_sup_right h2)

theorem raisesDegree (hR : Reduction O K l e a) (Sig : Finset (ZMod e)) (c : ZMod e) (A' : ℕ)
    (hA : 2 * A' ≤ l) (D : BKDat O K l e a ι η H)
    (hch : ∀ τ, D.desc.chars τ ⊆ (Sig : Set (ZMod e))) : RaisesDegree D.desc Sig c A' := by
  have hM := (hR.2.1 ι η H D).2.2 c
  have hl := (Fact.out : l.Prime).two_le
  have he := NeZero.pos e
  have hAl : A' < l := by omega
  set W := D.desc.isotypic c
  let V : ℕ → Submodule O (Vec K a ι) := fun i => part W (uL D.toPhiMod i) ⊔ part W (MMHigh D.toPhiMod)
  have hskip (i : ℕ) (hi : ¬ ∃ c' ∈ Sig, ∃ n : ℕ, i = (c - c').val + n * e) : V i ≤ V (i + 1) :=
    sup_le_sup_right (le_inf (graded D Sig hch c i hi) inf_le_right) _
  refine ⟨fun i hi => graded D Sig hch c i hi, fun x hx => ?_, fun x hx => ?_⟩
  · have hx0 : x ∈ V 0 := Submodule.mem_sup_left (Submodule.mem_inf.2
      ⟨mem_mulL.2 ⟨x, (Submodule.mem_inf.1 hx).1, by simp⟩, (Submodule.mem_inf.1 hx).2⟩)
    have h := climb D.toPhiMod.conn V 0 (e * A') (D₁ Sig c A')
      (fun i hi y hy => step hM i (by have := bounds_of_mem hi; nlinarith) y hy)
      (fun i _ h2 h3 => hskip i fun ⟨c', hc', n, hn⟩ => h3 (mem_degrees.2 ⟨c', hc', n,
        ⟨Nat.zero_le _, by have := ZMod.val_lt (c - c'); nlinarith⟩, hn.symm⟩))
      (fun i hi => by have := bounds_of_mem hi; exact Finset.mem_Ico.2 ⟨Nat.zero_le _, by nlinarith⟩) x hx0
    rw [zero_add] at h
    refine (sup_le_sup (inf_le_left.trans (le_of_eq (vL_eq _ _).symm)) inf_le_left) h
  · have hx0 : x ∈ V (e * A') := Submodule.mem_sup_left (by rwa [← vL_eq])
    have h := climb D.toPhiMod.conn V (e * A') (e * A') (D₂ Sig c A')
      (fun i hi y hy => step hM i (by have := bounds_of_mem hi; nlinarith) y hy)
      (fun i h1 h2 h3 => hskip i fun ⟨c', hc', n, hn⟩ => h3 (mem_degrees.2 ⟨c', hc', n,
        ⟨by have := ZMod.val_lt (c - c'); nlinarith, by nlinarith⟩, hn.symm⟩))
      (fun i hi => by have := bounds_of_mem hi; exact Finset.mem_Ico.2 ⟨by nlinarith, by nlinarith⟩) x hx0
    rw [show e * A' + e * A' = e * (2 * A') by ring] at h
    refine (sup_le_sup (inf_le_left.trans (le_of_eq (vL_eq _ _).symm)) inf_le_left) h

theorem degrees_of_reduction (hR : Reduction O K l e a) : Degrees O K l e a :=
  fun Sig c A' hA => ⟨degreeBounds Sig c A', fun ι _ _ η H D hch => raisesDegree hR Sig c A' hA D hch⟩

end Main

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.Degrees O K l e a :=
  fun O K _ _ _ _ _ _ l e a _ _ _ _ _ => degrees_of_reduction (GlobalTheory.T.monodromy_reduction_modulo_high_degree O K l e a)

end GlobalTheory.DegreeRaise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHom
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SubModel

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hg : IsHom A B g) :
    ∃ (K : Ob k G) (i : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A i ∧ Function.Injective i ∧ Function.Exact i g := by
  have hst : ∀ s : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (A.ρ s) := by
    intro s x hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
    rw [hg, hx, map_zero]
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker g) hst)
  refine ⟨K, (LinearMap.ker g).subtype ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_⟩
  · intro s x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← he]
    simp [Representation.subrepresentation]
  · exact (LinearMap.ker g).injective_subtype.comp e.symm.injective
  · intro y
    constructor
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact f q := by
  have hst : ∀ s : G, LinearMap.range f ≤ (LinearMap.range f).comap (B.ρ s) := by
    rintro s _ ⟨x, rfl⟩
    exact ⟨A.ρ s x, hf s x⟩
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range f) hst)
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range f).mkQ, ?_, ?_, ?_⟩
  · intro s x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    simp [Representation.quotient]
  · exact e.surjective.comp (LinearMap.range f).mkQ_surjective
  · intro y
    simp [Submodule.Quotient.mk_eq_zero]

theorem IsHom.comp' {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) := by
  intro s x
  simp only [LinearMap.comp_apply]
  rw [hf, hg]

theorem model_pre : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m), IsHom A B f → Function.Injective f → M.Model B N → M.Model A (F.pre A B f N) := by
  intro k G _ _ l n _ _ _ R F r Dt M A B f N hf hfi hN
  obtain ⟨C, Nb, A₁, j, p, hb, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨Q, q, hq, hqs, hfq⟩ := exists_coker A B f hf
  have hqp : IsHom A₁ Q (q ∘ₗ p) := IsHom.comp' hp hq
  obtain ⟨K, i, hi, hii, hex⟩ := exists_ker A₁ Q (q ∘ₗ p) hqp
  have hr : ∀ x, (p ∘ₗ i) x ∈ LinearMap.range f := fun x => (hfq _).1 ((hex _).2 ⟨x, rfl⟩)
  let p' : (Fin K.m → k) →ₗ[k] (Fin A.m → k) :=
    (LinearEquiv.ofInjective f hfi).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (p ∘ₗ i) hr
  have hfp : ∀ x, f (p' x) = p (i x) := by
    intro x
    have := congrArg Subtype.val ((LinearEquiv.ofInjective f hfi).apply_symm_apply
      (LinearMap.codRestrict _ (p ∘ₗ i) hr x))
    exact this
  have hp' : IsHom K A p' := by
    intro s x
    apply hfi
    rw [hfp, hf, hfp, hi, hp]
  have hp's : Function.Surjective p' := by
    intro a
    obtain ⟨y, hy⟩ := hps (f a)
    have : (q ∘ₗ p) y = 0 := by
      rw [LinearMap.comp_apply, hy]
      exact (hfq _).2 ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := (hex _).1 this
    exact ⟨x, hfi (by rw [hfp, hy])⟩
  have oC : F.Obj C := M.base_obj _ _ hb
  have o1 : F.Obj A₁ := F.obj_sub _ _ _ hj hji oC
  have oB : F.Obj B := F.obj_quot _ _ _ hp hps o1
  have oA : F.Obj A := F.obj_sub _ _ _ hf hfi oB
  have oK : F.Obj K := F.obj_sub _ _ _ hi hii o1
  have oQ : F.Obj Q := F.obj_quot _ _ _ hq hqs oB
  have hcomm : f ∘ₗ p' = p ∘ₗ i := LinearMap.ext hfp
  have hsq : ∀ a x, F.map A B f a (F.map K A p' a x) = F.map A₁ B p a (F.map K A₁ i a x) := by
    intro a x
    have h1 := F.map_comp K A B p' f oK oA oB hp' hf a
    have h2 := F.map_comp K A₁ B i p oK o1 oB hi hp a
    rw [hcomm, h2] at h1
    exact (LinearMap.congr_fun h1 x).symm
  have e1 := GlobalTheory.T.exact_map_of_exact F A B Q f q oB hf hq hfi hqs hfq
  have e2 := GlobalTheory.T.exact_map_of_exact F K A₁ Q i (q ∘ₗ p) o1 hi hqp hii (hqs.comp hps) hex
  refine ⟨C, Nb, K, j ∘ₗ i, p', hb, IsHom.comp' hi hj, hji.comp hii, hp', hp's, ?_⟩
  funext a
  ext x
  simp only [DFun.pre, DFun.push, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
    F.map_comp K A₁ C i j oK o1 oC hi hj a, LinearMap.comp_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : F.map A₁ Q (q ∘ₗ p) a y = 0 := by
      rw [F.map_comp A₁ B Q p q o1 oB oQ hp hq a, LinearMap.comp_apply, hyx]
      exact (e1 a _).2 ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (e2 a _).1 this
    exact ⟨z, hy, F.map_inj A B f oA oB hf hfi a (by rw [hsq, hyx])⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, (hsq a z).symm⟩

end GlobalTheory.Models.SubModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEnds
section
noncomputable section

open scoped Formalism.Per
open Filter Topology

namespace GlobalTheory.PMon.Gauss

theorem iSup_monomial_logConvex (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1)
    {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (⨆ n, c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n) ≤
      (⨆ n, c n * ρ₁ ^ n) ^ t * (⨆ n, c n * ρ₂ ^ n) ^ (1 - t) := by
  have hb : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → BddAbove (Set.range fun n => c n * ρ ^ n) := fun ρ h0' h1' =>
    ⟨1, Set.forall_mem_range.2 fun n => mul_le_one₀ (h1 n) (pow_nonneg h0' n) (pow_le_one₀ h0' h1')⟩
  apply ciSup_le
  intro n
  have hc : c n = c n ^ t * c n ^ (1 - t) := by
    rw [← Real.rpow_add' (h0 n) (by norm_num), add_sub_cancel, Real.rpow_one]
  have e : c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n = (c n * ρ₁ ^ n) ^ t * (c n * ρ₂ ^ n) ^ (1 - t) := by
    rw [Real.mul_rpow (h0 n) (pow_nonneg hρ₁ n), Real.mul_rpow (h0 n) (pow_nonneg hρ₂ n), mul_pow,
      Real.rpow_pow_comm hρ₁, Real.rpow_pow_comm hρ₂]
    conv_lhs => rw [hc]
    ring
  rw [e]
  have ht1' : 0 ≤ 1 - t := by linarith
  exact mul_le_mul
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₁ n)) (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n) ht0)
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) (le_ciSup (hb ρ₂ hρ₂ hρ₂1) n) ht1')
    (Real.rpow_nonneg (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) _)
    (Real.rpow_nonneg ((mul_nonneg (h0 n) (pow_nonneg hρ₁ n)).trans (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n)) _)

theorem gA_logConvex (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l) {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gA l (ρ₁ ^ t * ρ₂ ^ (1 - t)) a ≤ gA l ρ₁ a ^ t * gA l ρ₂ a ^ (1 - t) :=
  iSup_monomial_logConvex _ (fun n => by positivity)
    (fun n => Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
    hρ₁ hρ₂ hρ₁1 hρ₂1 ht0 ht1

theorem rpow_mul_rpow_one_sub_self {a t : ℝ} (ha : 0 ≤ a) : a ^ t * a ^ (1 - t) = a := by
  rw [← Real.rpow_add' ha (by norm_num), add_sub_cancel, Real.rpow_one]

theorem gC_logConvex : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ →
    ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  intro l _ x ρ₁ ρ₂ t h1 h12 h2 ht0 ht1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ₁ : 0 < ρ₁ := (inv_pos.2 hl0).trans_le h1
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le h12
  have ht1' : 0 ≤ 1 - t := by linarith
  set ρ := ρ₁ ^ t * ρ₂ ^ (1 - t) with hρdef
  have hρlo : ρ₁ ≤ ρ := by
    calc ρ₁ = ρ₁ ^ t * ρ₁ ^ (1 - t) := (rpow_mul_rpow_one_sub_self hρ₁.le).symm
      _ ≤ ρ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ₁.le h12 ht1') (Real.rpow_nonneg hρ₁.le _)
  have hρhi : ρ ≤ ρ₂ := by
    calc ρ ≤ ρ₂ ^ t * ρ₂ ^ (1 - t) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hρ₁.le h12 ht0) (Real.rpow_nonneg hρ₂.le _)
      _ = ρ₂ := rpow_mul_rpow_one_sub_self hρ₂.le
  have hρ0 : 0 < ρ := hρ₁.trans_le hρlo
  have G : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → IsGauss l σ (gC l σ) := fun σ a b => isGauss_gC_of_le l σ a b
  have Gl : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ (l : Formalism.Per.Acris l) = σ := by
    intro σ a b
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, (G σ a b).2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l ((inv_pos.2 hl0).le.trans a)
  have g : IsGauss l ρ (gC l ρ) := G ρ (h1.trans hρlo) (hρhi.trans_lt h2)
  have g₁ : IsGauss l ρ₁ (gC l ρ₁) := G ρ₁ h1 (h12.trans_lt h2)
  have g₂ : IsGauss l ρ₂ (gC l ρ₂) := G ρ₂ (h1.trans h12) h2

  have P : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → ∀ (k : ℕ) (y : Formalism.Per.Acris l),
      gC l σ ((l : Formalism.Per.Acris l) ^ k * y) = σ ^ k * gC l σ y := by
    intro σ a b k y
    rw [GlobalTheory.GaussSlope.map_pow_mul _ (G σ a b).2.2.2.1, Gl σ a b]

  have hs : ∀ s : Formalism.Per.Acris0 l, gC l ρ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ≤
      gC l ρ₁ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ t *
        gC l ρ₂ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ (1 - t) := by
    intro s
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have e : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → σ ^ k * gC l σ y = gA l σ a := by
      intro σ a' b
      rw [← P σ a' b, ha, (G σ a' b).2.2.2.2]
    have key := gA_logConvex l a hρ₁.le hρ₂.le (h12.trans h2.le) h2.le ht0 ht1
    rw [← e ρ (h1.trans hρlo) (hρhi.trans_lt h2), ← e ρ₁ h1 (h12.trans_lt h2), ← e ρ₂ (h1.trans h12) h2,
      Real.mul_rpow (pow_nonneg hρ₁.le _) (g₁.1 y).1, Real.mul_rpow (pow_nonneg hρ₂.le _) (g₂.1 y).1,
      ← Real.rpow_pow_comm hρ₁.le, ← Real.rpow_pow_comm hρ₂.le] at key
    have e2 : (ρ₁ ^ t) ^ k * gC l ρ₁ y ^ t * ((ρ₂ ^ (1 - t)) ^ k * gC l ρ₂ y ^ (1 - t)) =
        ρ ^ k * (gC l ρ₁ y ^ t * gC l ρ₂ y ^ (1 - t)) := by
      rw [hρdef, mul_pow]; ring
    rw [e2] at key
    exact le_of_mul_le_mul_left key (pow_pos hρ0 k)

  have F : ∀ r : ℕ, gC l ρ x ≤ max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r) := by
    intro r
    obtain ⟨s, z, hx⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have hz : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ ((l : Formalism.Per.Acris l) ^ r * z) ≤ σ ^ r := by
      intro σ a b
      rw [P σ a b]
      exact mul_le_of_le_one_right (pow_nonneg ((inv_pos.2 hl0).le.trans a) _) ((G σ a b).1 z).2
    have hy : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ y ≤ max (gC l σ x) (σ ^ r) := by
      intro σ a b
      have : y = x + -((l : Formalism.Per.Acris l) ^ r * z) := by rw [hx]; ring
      rw [this]
      refine ((G σ a b).2.1 _ _).trans (max_le_max le_rfl ?_)
      rw [(G σ a b).2.2.1]
      exact hz σ a b
    conv_lhs => rw [hx]
    refine (g.2.1 _ _).trans (max_le_max ?_ (hz ρ (h1.trans hρlo) (hρhi.trans_lt h2)))
    refine (hs s).trans (mul_le_mul (Real.rpow_le_rpow (g₁.1 y).1 (hy ρ₁ h1 (h12.trans_lt h2)) ht0)
      (Real.rpow_le_rpow (g₂.1 y).1 (hy ρ₂ (h1.trans h12) h2) ht1') (Real.rpow_nonneg (g₂.1 y).1 _)
      (Real.rpow_nonneg ((g₁.1 x).1.trans (le_max_left _ _)) _))
  have T : Tendsto (fun r : ℕ => max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r))
      atTop (𝓝 (max (max (gC l ρ₁ x) 0 ^ t * max (gC l ρ₂ x) 0 ^ (1 - t)) 0)) := by
    have t1 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₁.le (h12.trans_lt h2)
    have t2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₂.le h2
    have t0 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le (hρhi.trans_lt h2)
    exact ((((tendsto_const_nhds.max t1).rpow_const (Or.inr ht0)).mul
      ((tendsto_const_nhds.max t2).rpow_const (Or.inr ht1'))).max t0)
  have := ge_of_tendsto' T F
  rwa [max_eq_left (g₁.1 x).1, max_eq_left (g₂.1 x).1,
    max_eq_left (mul_nonneg (Real.rpow_nonneg (g₁.1 x).1 _) (Real.rpow_nonneg (g₂.1 x).1 _))] at this

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalIdealDiscreteFinite
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem quot_pow_maximalIdeal_discrete_finite :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O], PadicCoeff p O → ∀ k : ℕ,
      DiscreteTopology (O ⧸ IsLocalRing.maximalIdeal O ^ k) ∧ Finite (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  intro p O _ _ _ _ _ hO k
  haveI : CompactSpace O := hO.compact
  set I : Ideal O := IsLocalRing.maximalIdeal O ^ k with hI
  have hopen : IsOpen ((I : Ideal O) : Set O) := (isAdic_iff.mp hO.adic).1 k
  have hdisc : DiscreteTopology (O ⧸ I) := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have himg : (Ideal.Quotient.mk I) '' (I : Set O) = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
      · rintro rfl
        exact ⟨0, I.zero_mem, map_zero _⟩
    rw [← himg]
    exact QuotientRing.isOpenMap_coe I _ hopen
  refine ⟨hdisc, ?_⟩
  haveI : CompactSpace (O ⧸ I) := Quotient.compactSpace
  exact finite_of_compact_of_discrete

end GlobalTheory.NatQuot
end

