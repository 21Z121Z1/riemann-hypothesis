import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusOnStratifiedValue
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobValue

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem hf_comp {Q Q' : Obj l ↥(OL K)} (c : Hom Q Q') (g : Hom bk.prism Q) :
    BK.hf (c.comp g) = c.f.comp (BK.hf g) := rfl

theorem frob_change (S : Strat bk d) {Q : Obj l ↥(OL K)} (g g' : Hom bk.prism Q) (y y' : Fin d → Q.A)
    (hy : y = (S.ε g g').mulVec y') :
    BK.hf g' bk.E ^ S.a • (S.A.map (BK.hf g)).mulVec (fun i => Q.D.φ (y i)) =
      BK.hf g bk.E ^ S.a • (S.ε g g').mulVec ((S.A.map (BK.hf g')).mulVec (fun i => Q.D.φ (y' i))) := by
  have e : (fun i => Q.D.φ (y i)) = ((S.ε g g').map Q.D.φ).mulVec (fun i => Q.D.φ (y' i)) := by
    funext i; rw [hy, RingHom.map_mulVec]; rfl
  rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
    S.ε_φ]

theorem push (S : Strat bk d) {C Q : Obj l ↥(OL K)} (p : Hom C Q) (f : Hom bk.prism C) (c : C.A)
    (y : Fin d → C.A) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i)) =
      p.f c ^ S.a • (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) := by
  funext i
  have h1 : p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i) =
      p.f c ^ S.a * p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) := by
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
  have h2 : p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) =
      (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) i := by
    rw [RingHom.map_mulVec, Matrix.map_map, hf_comp]
    congr 1
    funext j
    exact p.f_φ (y j)
  refine h1.trans ?_
  simp only [h2, Pi.smul_apply, smul_eq_mul]

theorem vec_cancel {A : Type} [CommRing A] {r : A} (hr : r ∈ nonZeroDivisors A) {u w : Fin d → A}
    (e : r • u = r • w) : u = w :=
  funext fun i => (mul_cancel_left_mem_nonZeroDivisors hr).1 (congrFun e i)

theorem pow_smul_transfer_of_regular {A : Type} [CommRing A] {a : ℕ} {e e' u u' : A} {L R : Fin d → A}
    (hr : e ^ a * e' ^ a ∈ nonZeroDivisors A) (hF : e' ^ a • L = e ^ a • R) (hT : u * e = u' * e') :
    u ^ a • L = u' ^ a • R := by
  refine vec_cancel hr ?_
  calc (e ^ a * e' ^ a) • (u ^ a • L) = (u * e) ^ a • (e' ^ a • L) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring
    _ = (u' * e') ^ a • (e ^ a • R) := by rw [hF, hT]
    _ = (e ^ a * e' ^ a) • (u' ^ a • R) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring

theorem compat (S : Strat bk d) {B C Q : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (hn : ∀ g : Hom bk.prism Q, BK.hf g bk.E ∈ nonZeroDivisors Q.A)
    (x : N) (p q : Hom C Q) (hpq : p.comp h = q.comp h) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) =
      (S.ε (p.comp f) (q.comp f)).mulVec
        (fun i => q.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) := by
  have hY : ∀ j, p.f (V.v h f x j) = V.v (p.comp h) (p.comp f) x j :=
    fun j => (V.v_nat p h f x j).symm
  have hY' : ∀ j, q.f (V.v h f x j) = V.v (p.comp h) (q.comp f) x j := by
    rw [hpq]; exact fun j => (V.v_nat q h f x j).symm
  have hF := frob_change S (p.comp f) (q.comp f) _ _ (V.v_ε (p.comp h) (p.comp f) (q.comp f) x)
  have hT : p.f c * BK.hf (p.comp f) bk.E = q.f c * BK.hf (q.comp f) bk.E := by
    have e1 : p.f (c * BK.hf f bk.E) = q.f (c * BK.hf f bk.E) := by
      rw [hc]; exact congrArg (fun k : Hom B Q => k.f t) hpq
    simpa only [map_mul, hf_comp, RingHom.comp_apply] using e1
  rw [push S p f c, push S q f c, Matrix.mulVec_smul]
  simp only [hY, hY']
  exact pow_smul_transfer_of_regular (mul_mem (pow_mem (hn (p.comp f)) S.a) (pow_mem (hn (q.comp f)) S.a)) hF hT

theorem pow_smul_matrix_swap_of_relation {A : Type} [CommRing A] {a : ℕ} {e e' u : A} {L M : Fin d → A} {P : Matrix (Fin d) (Fin d) A}
    (hF : e' ^ a • L = e ^ a • P.mulVec M) : e ^ a • P.mulVec (u ^ a • M) = (u * e') ^ a • L := by
  rw [Matrix.mulVec_smul, mul_pow, mul_smul, hF, smul_comm]

theorem coord (S : Strat bk d) {B C Q Q' : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (a : Hom B Q) (g : Hom bk.prism Q) (h' : Hom Q Q') (a' : Hom C Q') (hcomm : a'.comp h = h'.comp a)
    (hinj' : Function.Injective h'.f) (x w : N)
    (hw : V.v h f w = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i))) :
    BK.hf g bk.E ^ S.a • V.v a g w = a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i) := by
  have nat' : ∀ (y : N) j, h'.f (V.v a g y j) = V.v (a'.comp h) (h'.comp g) y j := by
    intro y j; rw [hcomm]; exact (V.v_nat h' a g y j).symm
  have natC : ∀ (y : N) j, a'.f (V.v h f y j) = V.v (a'.comp h) (a'.comp f) y j :=
    fun y j => (V.v_nat a' h f y j).symm
  have ht : h'.f (a.f t) = a'.f c * BK.hf (a'.comp f) bk.E := by
    have e : h'.f (a.f t) = a'.f (h.f t) := congrArg (fun k : Hom B Q' => k.f t) hcomm.symm
    rw [e, ← hc, map_mul]; rfl
  have e1 : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      BK.hf (h'.comp g) bk.E ^ S.a • V.v (a'.comp h) (h'.comp g) w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, nat']
    rfl
  have e2 : V.v (a'.comp h) (a'.comp f) w =
      a'.f c ^ S.a • (S.A.map (BK.hf (a'.comp f))).mulVec fun j => Q'.D.φ (V.v (a'.comp h) (a'.comp f) x j) := by
    have e := push S a' f c (V.v h f x)
    rw [← hw] at e
    simp only [natC] at e
    exact e
  have e3 := push S h' g (a.f t) (V.v a g x)
  simp only [nat', ht] at e3
  have hF := frob_change S (h'.comp g) (a'.comp f) _ _ (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) x)
  have key : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      fun i => h'.f ((a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun j => Q.D.φ (V.v a g x j)) i) := by
    have v1 := (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) w).trans (congrArg _ e2)
    exact e1.trans ((congrArg (fun v => BK.hf (h'.comp g) bk.E ^ S.a • v) v1).trans ((pow_smul_matrix_swap_of_relation hF).trans e3.symm))
  funext i
  exact hinj' (congrFun key i)

theorem psi_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I →
    ∃ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ := by
  intro l _ K bk d S B N _ _ V t ht
  obtain ⟨C, h, ⟨f⟩, hC⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hIC := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f).1
  have htC : h.f t ∈ Ideal.span {BK.hf f bk.E} := hIC ▸ h.f_I t ht
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 htC
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V h f hC
  have hzc : ∀ x : N, ∃ y, V.v h f y = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i)) :=
    fun x => hsurj _ fun Q p q hpq =>
      compat S V h f c t hc (fun g => (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2) x p q hpq
  choose Ψf hΨf using hzc
  have zadd : ∀ x y : N, Ψf (x + y) = Ψf x + Ψf y := by
    intro x y
    apply hinj
    have e1 : V.v h f (x + y) = V.v h f x + V.v h f y := map_add (V.v h f) x y
    have e2 : V.v h f (Ψf x + Ψf y) = V.v h f (Ψf x) + V.v h f (Ψf y) := map_add (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (x + y) i)) =
        (fun i => C.D.φ (V.v h f x i)) + (fun i => C.D.φ (V.v h f y i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans (C.D.φ.map_add _ _)
    refine (hΨf (x + y)).trans (Eq.trans ?_ ((congrArg₂ (· + ·) (hΨf x) (hΨf y)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_add _ _ _)).trans (smul_add _ _ _)
  have zsmul : ∀ (b : B.A) (x : N), Ψf (b • x) = B.D.φ b • Ψf x := by
    intro b x
    apply hinj
    have e1 : V.v h f (b • x) = h.f b • V.v h f x := LinearMap.map_smulₛₗ (V.v h f) b x
    have e2 : V.v h f (B.D.φ b • Ψf x) = h.f (B.D.φ b) • V.v h f (Ψf x) := LinearMap.map_smulₛₗ (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (b • x) i)) = h.f (B.D.φ b) • (fun i => C.D.φ (V.v h f x i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans
        ((C.D.φ.map_mul _ _).trans (congrArg (· * C.D.φ (V.v h f x i)) (h.f_φ b).symm))
    refine (hΨf (b • x)).trans (Eq.trans ?_ ((congrArg (h.f (B.D.φ b) • ·) (hΨf x)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_smul _ _ _)).trans (smul_comm _ _ _)
  refine ⟨{ toFun := Ψf, map_add' := zadd, map_smul' := zsmul }, ?_⟩
  intro Q a g x
  obtain ⟨Q', h', a', hcomm, hinj'⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hC Q a
  exact coord S V h f c t hc a g h' a' hcomm hinj' x (Ψf x) (hΨf x)

end GlobalTheory.BSP.FrobValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ρ : IrrGL k} {hρ : ρ.IsCusp} {c d c' d' : ℤ} {h : c ≤ d} {h' : c' ≤ d'} {Δ Δ' : Segment k}

theorem first_mem_carrier (Δ : Segment k) : Δ.first ∈ Δ.carrier := mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩

theorem nu_mem_icc {a : ℤ} : ρ.nu a ∈ (icc ρ hρ c d h).carrier ↔ c ≤ a ∧ a ≤ d := by
  simp only [mem_icc, IrrGL.nu_intCast_inj hρ.1]
  exact ⟨fun ⟨_, h1, h2, e⟩ => e ▸ ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨a, h1, h2, rfl⟩⟩

theorem eq_icc_of_first_eq (hρ : ρ.IsCusp) (e : Δ.first = ρ.nu c) :
    Δ = icc ρ hρ c (c + Δ.len - 1) (Int.le_sub_one_of_lt (lt_add_of_pos_right c (Nat.cast_pos.2 Δ.len_pos))) :=
  ext_first e (by simp only [icc, len_ofFirst]; omega)

theorem exists_eq_icc_of_mem (hρ : ρ.IsCusp) {a : ℤ} (ha : ρ.nu a ∈ Δ.carrier) :
    ∃ (c d : ℤ) (h : c ≤ d), Δ = icc ρ hρ c d h := by
  obtain ⟨b, -, hb⟩ := mem_carrier.1 ha
  refine ⟨a - b, _, _, eq_icc_of_first_eq hρ ?_⟩
  have := congrArg (fun x => IrrGL.nu x (-(b : ℂ))) hb
  simpa [sub_eq_add_neg] using this

theorem icc_subset_icc : (icc ρ hρ c d h).carrier ⊆ (icc ρ hρ c' d' h').carrier ↔ c' ≤ c ∧ d ≤ d' := by
  refine ⟨fun H => ⟨(nu_mem_icc.1 (H (nu_mem_icc.2 ⟨le_rfl, h⟩))).1, (nu_mem_icc.1 (H (nu_mem_icc.2 ⟨h, le_rfl⟩))).2⟩,
    fun ⟨h1, h2⟩ x hx => ?_⟩
  obtain ⟨a, h3, h4, rfl⟩ := mem_icc.1 hx
  exact nu_mem_icc.2 ⟨h1.trans h3, h4.trans h2⟩

theorem exists_carrier_eq_union_icc :
    (∃ Γ : Segment k, Γ.carrier = (icc ρ hρ c d h).carrier ∪ (icc ρ hρ c' d' h').carrier) ↔
      c' ≤ d + 1 ∧ c ≤ d' + 1 := by
  constructor
  · rintro ⟨Γ, hΓ⟩
    obtain ⟨e, f, hef, rfl⟩ := exists_eq_icc_of_mem (Δ := Γ) hρ (a := c)
      (by rw [hΓ]; exact Or.inl (nu_mem_icc.2 ⟨le_rfl, h⟩))
    have key : ∀ a : ℤ, (e ≤ a ∧ a ≤ f) ↔ (c ≤ a ∧ a ≤ d) ∨ (c' ≤ a ∧ a ≤ d') := fun a => by
      simpa only [Set.mem_union, nu_mem_icc] using Set.ext_iff.1 hΓ (ρ.nu a)
    have := key c; have := key d'; have := key c'; have := key d; have := key (d + 1); have := key (d' + 1)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨icc ρ hρ (min c c') (max d d') (by omega), Set.ext fun x => ?_⟩
    simp only [Set.mem_union, mem_icc]
    constructor
    · rintro ⟨a, h3, h4, rfl⟩
      by_cases ha : c ≤ a ∧ a ≤ d
      · exact Or.inl ⟨a, ha.1, ha.2, rfl⟩
      · exact Or.inr ⟨a, by omega, by omega, rfl⟩
    · rintro (⟨a, h3, h4, rfl⟩ | ⟨a, h3, h4, rfl⟩) <;> exact ⟨a, by omega, by omega, rfl⟩

theorem linked_icc : (icc ρ hρ c d h).Linked (icc ρ hρ c' d' h') ↔
    (c < c' ∧ c' ≤ d + 1 ∧ d < d') ∨ (c' < c ∧ c ≤ d' + 1 ∧ d' < d) := by
  rw [Linked, exists_carrier_eq_union_icc, icc_subset_icc, icc_subset_icc]
  omega

theorem precedes_icc : (icc ρ hρ c d h).Precedes (icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d' := by
  have key : (∃ j : ℕ, 0 < j ∧ (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j) ↔ c < c' := by
    have e : ∀ j : ℕ, (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j ↔ c' = c + j := fun j => by
      rw [← IrrGL.nu_intCast_inj hρ.1]
      simp [icc]
    simp only [e]
    exact ⟨fun ⟨j, h1, h2⟩ => by omega, fun H => ⟨(c' - c).toNat, by omega, by omega⟩⟩
  rw [Precedes, linked_icc, key]
  omega

theorem Linked.exists_eq_icc (H : Linked Δ Δ') : ∃ (ρ : IrrGL k) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
    Δ = icc ρ hρ c d h ∧ Δ' = icc ρ hρ c' d' h' := by
  obtain ⟨⟨Γ, hΓ⟩, -⟩ := H
  have key : ∀ D : Segment k, D.carrier ⊆ Γ.carrier → ∃ (c d : ℤ) (h : c ≤ d), D = icc Γ.first Γ.isCusp_first c d h :=
    fun D hD => by
      obtain ⟨a, -, ha⟩ := mem_carrier.1 (hD D.first_mem_carrier)
      exact ⟨a, _, _, eq_icc_of_first_eq _ (by simpa using ha.symm)⟩
  obtain ⟨c, d, h, e⟩ := key Δ (hΓ ▸ Set.subset_union_left)
  obtain ⟨c', d', h', e'⟩ := key Δ' (hΓ ▸ Set.subset_union_right)
  exact ⟨_, _, c, d, c', d', h, h', e, e'⟩

theorem linked_iff_precedes : Linked Δ Δ' ↔ Precedes Δ Δ' ∨ Precedes Δ' Δ := by
  refine ⟨fun H => ?_, fun H => H.elim (·.1) (·.1.symm)⟩
  obtain ⟨ρ, hρ, c, d, c', d', h, h', rfl, rfl⟩ := H.exists_eq_icc
  simpa only [precedes_icc] using linked_icc.1 H

theorem precedes_iff : Precedes Δ Δ' ↔
    ∃ j : ℕ, 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len ∧ Δ'.first = Δ.first.nu j := by
  have key : ∀ j : ℕ, Δ'.first = Δ.first.nu j → (Precedes Δ Δ' ↔ 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len) := fun j e => by
    have e1 := eq_icc_of_first_eq (Δ := Δ) (c := 0) Δ.isCusp_first (by simp)
    have e2 := eq_icc_of_first_eq (Δ := Δ') (c := j) Δ.isCusp_first (by simpa using e)
    refine (iff_of_eq (congrArg₂ Precedes e1 e2)).trans (precedes_icc.trans ?_)
    omega
  refine ⟨fun H => ?_, fun ⟨j, h1, h2, h3, e⟩ => (key j e).2 ⟨h1, h2, h3⟩⟩
  obtain ⟨j, -, e⟩ := H.2
  obtain ⟨h1, h2, h3⟩ := (key j e).1 H
  exact ⟨j, h1, h2, h3, e⟩

theorem exists_first_eq_of_transGen (H : Relation.TransGen Precedes Δ Δ') :
    ∃ j : ℕ, 0 < j ∧ Δ'.first = Δ.first.nu j := by
  induction H with
  | single H => exact H.2
  | tail _ H ih =>
    obtain ⟨i, hi, e⟩ := ih
    obtain ⟨j, -, e'⟩ := H.2
    exact ⟨i + j, by omega, by rw [e', e, IrrGL.nu_nu, Nat.cast_add]⟩

theorem not_transGen_precedes_self (Δ : Segment k) : ¬ Relation.TransGen Precedes Δ Δ := fun H => by
  obtain ⟨j, hj, e⟩ := exists_first_eq_of_transGen H
  exact hj.ne ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by simpa using e))

theorem Precedes.asymm (H : Precedes Δ Δ') : ¬ Precedes Δ' Δ := fun H' =>
  not_transGen_precedes_self Δ ((Relation.TransGen.single H).tail H')

theorem lt_of_precedes_nu {x y : ℝ} (H : (Δ.nu x).Precedes (Δ.nu y)) : x < y := by
  obtain ⟨-, j, hj, e⟩ := H
  have e' : Δ.first.nu y = Δ.first.nu ((x + j : ℝ) : ℂ) := by
    push_cast
    exact e.trans (Δ.first.nu_nu x j)
  have : (0 : ℝ) < j := Nat.cast_pos.2 hj
  rw [(IrrGL.nu_ofReal_inj Δ.isCusp_first.1).1 e']
  linarith

theorem not_precedes_nu (Δ : Segment k) {x y : ℝ} (hxy : y < x) : ¬ (Δ.nu x).Precedes (Δ.nu y) := fun H =>
  hxy.asymm (lt_of_precedes_nu H)

theorem tw_injective (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Function.Injective fun Δ : Segment k => Δ.tw χ hχ :=
  Function.LeftInverse.injective (g := fun x => x.tw χ⁻¹ hχ.inv) fun x => x.tw_tw_inv χ hχ

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

theorem exists_list_pairwise_not_rel {α : Type*} {r : α → α → Prop} (hr : ∀ a, ¬ Relation.TransGen r a a)
    (m : Multiset α) : ∃ l : List α, (l : Multiset α) = m ∧ l.Pairwise fun a b => ¬ r a b := by
  classical
  let p : α → α → Prop := fun a b => Relation.ReflTransGen r b a
  haveI : IsPartialOrder α p :=
    { refl := fun _ => .refl
      trans := fun _ _ _ h h' => h'.trans h
      antisymm := fun a b h h' => by
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h
        · exact e
        · exact absurd (h.trans_left h') (hr _) }
  obtain ⟨s, hs, hps⟩ := extend_partialOrder p
  refine ⟨m.sort s, m.sort_eq s, (m.pairwise_sort s).imp fun {a b} hab h => ?_⟩
  obtain rfl : a = b := antisymm hab (hps _ _ (.single h))
  exact hr a (.single h)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOrderedForm (𝔪 : Multiset (Segment k)) :
    ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪 := by
  obtain ⟨l, rfl, hl⟩ := exists_list_pairwise_not_rel Segment.not_transGen_precedes_self 𝔪
  exact ⟨l.get, (Fin.univ_val_map l.get).trans (congrArg _ (List.ofFn_get l)), List.pairwise_iff_get.1 hl⟩

theorem isOrderedForm_tw_iff {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)} (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪 :=
  ⟨fun H => by simpa only [Multiset.map_map, Function.comp_def, Segment.tw_tw_inv, Multiset.map_id'] using H.tw χ⁻¹ hχ.inv,
    fun H => H.tw χ hχ⟩

theorem precedes_and_orderedForms (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    ((∀ Δ Δ' : Segment k, Δ.Precedes Δ' → ¬ Δ'.Precedes Δ) ∧
      (∀ Δ : Segment k, ¬ Relation.TransGen Segment.Precedes Δ Δ) ∧
      ∀ 𝔪 : Multiset (Segment k), ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪) ∧
    ((∀ (ρ : IrrGL k) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
        (Segment.icc ρ hρ c d h).Precedes (Segment.icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d') ∧
      ∀ Δ Δ' : Segment k, Δ.Linked Δ' ↔ Δ.Precedes Δ' ∨ Δ'.Precedes Δ) ∧
    (∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Linked (Δ'.tw χ hχ) ↔ Δ.Linked Δ') ∧
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Precedes (Δ'.tw χ hχ) ↔ Δ.Precedes Δ') ∧
      ∀ (h : ℕ) (Δ : Fin h → Segment k) (𝔪 : Multiset (Segment k)),
        IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪) ∧
    ∀ (Δ : Segment k) (x y : ℝ), y < x → ¬ (Δ.nu x).Precedes (Δ.nu y) :=
  ⟨⟨fun _ _ => Segment.Precedes.asymm, Segment.not_transGen_precedes_self, exists_isOrderedForm⟩,
    ⟨fun _ _ _ _ _ _ _ _ => Segment.precedes_icc, fun _ _ => Segment.linked_iff_precedes⟩,
    fun χ hχ => ⟨fun _ _ => Segment.linked_tw_iff χ hχ, fun _ _ => Segment.precedes_tw_iff χ hχ,
      fun _ _ _ => isOrderedForm_tw_iff χ hχ⟩,
    fun Δ _ _ h => Δ.not_precedes_nu h⟩

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalUnitaryEmbeddingDefiniteUnitaryNonspl
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG

namespace GlobalTheory.UnitaryBC.NonSplit

variable {E : Type} [Field E] [NumberField E]

theorem matrix_ext_pLoc {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Af E)}
    (H : ∀ u : HeightOneSpectrum (𝓞 E), A.map (pLoc E u) = B.map (pLoc E u)) : A = B :=
  Matrix.ext fun i j => FiniteAdeleRing.ext E fun u => congrFun₂ (H u) i j

theorem continuous_finGL' (n : ℕ) : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem eq_conjSrc_self (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x)) (hv : ∀ x, Valued.v (s x) = Valued.v x) :
    w = conjSrc c w := by
  refine eq_conjSrc fun k => ?_
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (c k)) = w.valuation E (c k) :=
    w.valuedAdicCompletion_eq_valuation' _
  rw [← h1, ← h2, ← hs, hv]

theorem cT_locGL_mul (c : E ≃+* E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E) (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (c x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E)) (hg : cT s g.val * g.val = 1) :
    cT (conjFin c) (locGL E n w g).val * (locGL E n w g).val = 1 := by
  refine matrix_ext_pLoc fun u => ?_
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  by_cases hu : u = w
  · subst hu
    have e1 : (locGL E n u g).val.map (pLoc E u) = g.val := congrArg Units.val (pLoc_locGL u g)
    have e2 : (cT (conjFin c) (locGL E n u g).val).map (pLoc E u) = cT s g.val := by
      ext1 i j
      change pLoc E u (conjFin c ((locGL E n u g).val j i)) = s (g.val j i)
      rw [← e1]
      exact pLoc_conjFin_eq c u s hs hv _
    rw [e1, e2, hg]
  · have hne : conjSrc c u ≠ w := fun e =>
      hu (conjSrc_injective c (e.trans (eq_conjSrc_self c w s hs hv)))
    have e1 : (locGL E n w g).val.map (pLoc E u) = 1 := congrArg Units.val (pLoc_locGL_of_ne hu g)
    have e3 : (locGL E n w g).val.map (pLoc E (conjSrc c u)) = 1 := congrArg Units.val (pLoc_locGL_of_ne hne g)
    have e2 : (cT (conjFin c) (locGL E n w g).val).map (pLoc E u) = 1 := by
      ext1 i j
      change conjLoc c u (((locGL E n w g).val.map (pLoc E (conjSrc c u))) j i) = _
      rw [e3]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply, hij, Ne.symm hij]
    rw [e1, e2, Matrix.mul_one]

variable [IsCMField E]

theorem finGL_locGL_mem_UA {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E)) (hg : cT s g.val * g.val = 1) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  have h1 : (finGL E n (locGL E n w g)).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL (locGL E n w g))
  have h2 : (finGL E n (locGL E n w g)).val.map (pFin E) = (locGL E n w g).val :=
    congrArg Units.val (pFin_finGL (locGL E n w g))
  have h3 : (cT (conjAd E) (finGL E n (locGL E n w g)).val).map (pInf E) = 1 := by
    ext1 i j
    change (infEq E).symm ((infEq E) (starRingEnd (Cinf E) (pInf E ((finGL E n (locGL E n w g)).val j i)))) = _
    rw [RingEquiv.symm_apply_apply]
    change starRingEnd (Cinf E) (((finGL E n (locGL E n w g)).val.map (pInf E)) j i) = _
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  have h4 : (cT (conjAd E) (finGL E n (locGL E n w g)).val).map (pFin E) =
      cT (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E n w g).val := by
    ext1 i j
    change conjFin _ (((finGL E n (locGL E n w g)).val.map (pFin E)) j i) = _
    rw [h2]
    rfl
  have h5 := cT_locGL_mul (IsCMField.complexConj E).toRingEquiv w s hs hv g hg
  have h6 : (cT (conjAd E) (finGL E n (locGL E n w g)).val * (finGL E n (locGL E n w g)).val).map (pInf E) =
      (1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) := by
    rw [Matrix.map_mul, h3, h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have h7 : (cT (conjAd E) (finGL E n (locGL E n w g)).val * (finGL E n (locGL E n w g)).val).map (pFin E) =
      (1 : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) := by
    rw [Matrix.map_mul, h4, h2, h5, Matrix.map_one _ (map_zero _) (map_one _)]
  ext1 i j
  exact ad_ext (congrFun₂ h6 i j) (congrFun₂ h7 i j)

end GlobalTheory.UnitaryBC.NonSplit

open GlobalTheory.UnitaryBC.NonSplit in

theorem GlobalTheory.UnitaryBC.exists_locUnitary_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) → ¬ IsSplitAt w →
    ∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧
      (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧
      ∀ x g, cLoc w x = 1 → x * ι g = ι g * x := by
  intro E _ _ _ n w s hs hv hns
  have hU : ∀ g : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      finGL E n (locGL E n w g.1) ∈ UA E n := fun g => by
    refine finGL_locGL_mem_UA w s hs hv g.1 ?_
    have h : cT s g.1.val * 1 * g.1.val = 1 := g.2
    rwa [Matrix.mul_one] at h
  refine ⟨((finGL E n).comp ((locGL E n w).comp (Formalism.UG.UJ s 1).subtype)).codRestrict (UA E n) hU,
    Continuous.subtype_mk (((continuous_finGL' n).comp (CuspSub.continuous_locGL w)).comp continuous_subtype_val) _,
    fun g => ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 ?_, Subgroup.mem_iInf.2 fun u =>
      Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩, ?_⟩, fun x hx h1 => ?_, fun x g h1 => ?_⟩
  · change GeneralLinearGroup.map (pInf E) (finGL E n (locGL E n w g.1)) = 1
    exact pInf_finGL _
  · change GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) (finGL E n (locGL E n w g.1))) = 1
    rw [pFin_finGL]
    exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
  · change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (finGL E n (locGL E n w g.1))) = g.1
    rw [pFin_finGL, pLoc_locGL]
  · obtain ⟨hxf, hxi⟩ := Subgroup.mem_inf.1 hx
    have hinf : GeneralLinearGroup.map (pInf E) x.1 = 1 := MonoidHom.mem_ker.1 hxf
    have hloc : ∀ u, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) x.1) = 1 := fun u => by
      by_cases hu : u = w
      · subst hu; exact h1
      · have hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun e => hns ⟨u, hu, e⟩
        exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hxi u) hu')
    refine Subtype.ext (ga_ext (hinf.trans (map_one _).symm) ?_)
    change _ = GeneralLinearGroup.map (pFin E) 1
    rw [map_one]
    exact LocUniq.gl_ext fun u => by rw [hloc u, map_one]
  · have hk : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x.1) = 1 := h1
    apply Subtype.ext
    change x.1 * finGL E n (locGL E n w g.1) = finGL E n (locGL E n w g.1) * x.1
    obtain ⟨y, k, hx, hk'⟩ : ∃ y k, x.1 = infGL E n y * finGL E n k ∧ GeneralLinearGroup.map (pLoc E w) k = 1 :=
      ⟨_, _, (infGL_mul_finGL x.1).symm, hk⟩
    rw [hx, mul_assoc, ← map_mul, LocUniq.comm_locGL w hk' g.1, map_mul, ← mul_assoc, infGL_comm, mul_assoc]

end
end

