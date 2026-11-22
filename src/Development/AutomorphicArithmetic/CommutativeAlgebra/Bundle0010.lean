import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0009
import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.A6supp
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineHomExistsUniqueOfGlobalSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private theorem comp_gamma {T : Scheme.{0}} (φ : Polynomial ℤ →+* Γ(T, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫
      (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ := by
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  erw [Scheme.ΓSpecIso_naturality]
  exact Iso.inv_hom_id_assoc _ _

theorem UpperTheory.affineLine_hom_existsUnique_of_globalSection :
    ∀ (T : Scheme.{0}) (a : Γ(T, ⊤)), ∃! s : T ⟶ A1, s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X) = a := by
  intro T a
  have key : ∀ s : T ⟶ A1, s = T.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫ s.appTop) := by
    intro s
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  let φ : Polynomial ℤ →+* Γ(T, ⊤) := Polynomial.eval₂RingHom (Int.castRingHom _) a
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · have h : ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫
        (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop).hom Polynomial.X = a := by
      rw [comp_gamma]
      simp [φ]
    rw [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h
  · intro s hs
    suffices e : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫ s.appTop =
        CommRingCat.ofHom φ by
      rw [key s, e]
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · rw [CommRingCat.hom_comp, RingHom.comp_apply, hs]
      simp [φ]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CochainPullbackBijectiveOfTermwiseBijectiveInjec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.TruncCx

open GlobalTheory.ColFilt

section Abstract

variable {A B : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]

private def ConeAt (dA : ∀ n m, A n →+ A m) (dB : ∀ n m, B n →+ B m) (Φ : ∀ n, A n →+ B n)
    (n₂ : ℤ) : Prop :=
  ∀ n₀ n₁ n₃ : ℤ, n₀ + 1 = n₁ → n₁ + 1 = n₂ → n₂ + 1 = n₃ → ∀ (x : A n₂) (y : B n₁),
    dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w

variable {GA GB : ℤ → ℤ → Type*} [∀ p n, AddCommGroup (GA p n)] [∀ p n, AddCommGroup (GB p n)]
  {dA : ∀ n m, A n →+ A m} {gA : ∀ p n m, GA p n →+ GA p m} {FA : ℤ → ∀ n, AddSubgroup (A n)}
  {rA : ∀ p n m, n + p = m → (A n →+ GA p m)}
  {dB : ∀ n m, B n →+ B m} {gB : ∀ p n m, GB p n →+ GB p m} {FB : ℤ → ∀ n, AddSubgroup (B n)}
  {rB : ∀ p n m, n + p = m → (B n →+ GB p m)}

private theorem coneAt_of_graded (hA : IsFilt dA gA FA rA) (hB : IsFilt dB gB FB rB)
    (Φ : ∀ n, A n →+ B n)
    (hd : ∀ n m, n + 1 = m → ∀ x, Φ m (dA n m x) = dB n m (Φ n x))
    (hF : ∀ p n, ∀ x ∈ FA p n, Φ n x ∈ FB p n) (Ψ : ∀ p m, GA p m →+ GB p m)
    (hΨ : ∀ p n m (h : n + p = m), ∀ x ∈ FA p n, Ψ p m (rA p n m h x) = rB p n m h (Φ n x))
    (M : ℤ) (hc : ∀ p ≤ 0, ∀ k ≤ M + p, ConeAt (gA p) (gB p) (Ψ p) k)
    (n₂ : ℤ) (hn : n₂ ≤ M) : ConeAt dA dB Φ n₂ := by
  intro n₀ n₁ n₃ h01 h12 h23
  obtain ⟨N1, hN1⟩ := hA.bot n₂
  obtain ⟨N2, hN2⟩ := hB.bot n₁
  have key : ∀ p, min (min N1 N2) 0 ≤ p → p ≤ 0 → ∀ (x : A n₂) (y : B n₁), x ∈ FA p n₂ →
      y ∈ FB p n₁ → dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w := by
    intro p hNp
    induction p, hNp using Int.le_induction with
    | base =>
      intro _ x y hxF hyF _ _
      have hx0 : x = 0 := hN1 x (hA.mono _ N1 n₂ (by omega) hxF)
      have hy0 : y = 0 := hN2 y (hB.mono _ N2 n₁ (by omega) hyF)
      exact ⟨0, 0, by simp [hx0], by simp [hy0]⟩
    | succ q hNq ih =>
      intro hq x y hxF hyF hx hxy
      have ih' := ih (by omega)
      have hpq : q + 1 - 1 = q := by ring
      obtain ⟨v₀, w₀, hv₀, hw₀⟩ := hc (q + 1) hq (n₂ + (q + 1)) (by omega)
        (n₀ + (q + 1)) (n₁ + (q + 1)) (n₃ + (q + 1)) (by omega) (by omega) (by omega)
        (rA (q + 1) n₂ _ rfl x) (rB (q + 1) n₁ _ rfl y)
        (by rw [← hA.rd (q + 1) n₂ n₃ _ _ rfl rfl h23 x hxF, hx, map_zero])
        (by rw [hΨ (q + 1) n₂ _ rfl x hxF, hxy, hB.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 y hyF])
      obtain ⟨v, hvF, hv⟩ := hA.surj (q + 1) n₁ _ rfl v₀
      obtain ⟨w, hwF, hw⟩ := hB.surj (q + 1) n₀ _ rfl w₀
      have hx'F : x - dA n₁ n₂ v ∈ FA q n₂ := by
        have h := (hA.ker (q + 1) n₂ _ rfl (x - dA n₁ n₂ v)
          (sub_mem hxF (hA.dF (q + 1) n₁ n₂ h12 v hvF))).1
          (by rw [map_sub, hA.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 v hvF, hv, hv₀, sub_self])
        rwa [hpq] at h
      have hy'F : y - Φ n₁ v - dB n₀ n₁ w ∈ FB q n₁ := by
        have h := (hB.ker (q + 1) n₁ _ rfl (y - Φ n₁ v - dB n₀ n₁ w)
          (sub_mem (sub_mem hyF (hF (q + 1) n₁ v hvF)) (hB.dF (q + 1) n₀ n₁ h01 w hwF))).1
          (by
            rw [map_sub, map_sub, ← hΨ (q + 1) n₁ _ rfl v hvF,
              hB.rd (q + 1) n₀ n₁ _ _ rfl rfl h01 w hwF, hv, hw, hw₀]
            abel)
        rwa [hpq] at h
      have hx'c : dA n₂ n₃ (x - dA n₁ n₂ v) = 0 := by
        rw [map_sub, hx, hA.dd, sub_self]
      have hx'r : Φ n₂ (x - dA n₁ n₂ v) = dB n₁ n₂ (y - Φ n₁ v - dB n₀ n₁ w) := by
        rw [map_sub, map_sub, map_sub, hd n₁ n₂ h12 v, hxy, hB.dd, sub_zero]
      obtain ⟨v', w', hv', hw'⟩ := ih' _ _ hx'F hy'F hx'c hx'r
      refine ⟨v + v', w + w', ?_, ?_⟩
      · rw [map_add, ← hv']
        abel
      · rw [map_add, map_add]
        rw [sub_sub, sub_eq_iff_eq_add] at hw'
        rw [hw']
        abel
  intro x y hx hxy
  exact key 0 (by omega) le_rfl x y (hA.top n₂ x) (hB.top n₁ y) hx hxy

end Abstract

section Classes

variable {R : Type} [CommRing R]

private def pre {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) : Cochain L I n →+ Cochain K I n :=
  AddMonoidHom.mk' (fun α => (Cochain.ofHom g).comp α (zero_add n))
    (fun _ _ => Cochain.comp_add _ _ _ _)

private theorem pre_v {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) (α : Cochain L I n) (t q : ℤ)
    (hq : t + n = q) : (pre g I n α).v t q hq = g.f t ≫ α.v t q hq := by
  simp [pre, Cochain.comp_zero_cochain_v]

private theorem pre_δ {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n m : ℤ) (h : n + 1 = m)
    (α : Cochain L I n) : pre g I m (δ n m α) = δ n m (pre g I n α) := by
  simp only [pre, AddMonoidHom.mk'_apply]
  rw [δ_ofHom_comp]

private theorem cpull_mk_eq_mk_of_pre {K L I : Cx R} (g : K ⟶ L) (n : ℤ) (x : Cocycle L I n)
    (z : Cocycle K I n) (hz : (z : Cochain K I n) = pre g I n x) :
    cpull g I n (CohomologyClass.mk x) = CohomologyClass.mk z := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  exact Subtype.ext (by rw [hz]; rfl)

private theorem coneAt_of_conn {K L I : Cx R} (g : K ⟶ L) (M : ℤ)
    (hb : ∀ n, n < M → Function.Bijective (cpull g I n)) (hi : Function.Injective (cpull g I M))
    (k : ℤ) (hk : k ≤ M) : ConeAt (dC L I) (dC K I) (pre g I) k := by
  intro n₀ n₁ n₃ h01 h12 h23 x y hx hxy
  simp only [dC, AddMonoidHom.mk'_apply] at hx hxy ⊢
  have hk1 : n₁ < M := by omega
  have injk : Function.Injective (cpull g I k) := by
    rcases lt_or_eq_of_le hk with h | h
    · exact (hb k h).1
    · subst h
      exact hi
  have hpx : δ k n₃ (pre g I k x) = 0 := by rw [← pre_δ g I k n₃ h23, hx, map_zero]
  have e1 : cpull g I k (CohomologyClass.mk (Cocycle.mk x n₃ h23 hx)) = 0 := by
    rw [cpull_mk_eq_mk_of_pre g k _ (Cocycle.mk (pre g I k x) n₃ h23 hpx) rfl, ← CohomologyClass.mk_zero,
      mk_eq_mk_iff _ _ n₁ h12]
    exact ⟨y, by simp [hxy]⟩
  have e2 := injk (e1.trans (map_zero _).symm)
  rw [← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ n₁ h12] at e2
  obtain ⟨v', hv'⟩ := e2
  simp only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hv'
  have hyc : δ n₁ k (y - pre g I n₁ v') = 0 := by
    rw [δ_sub, ← pre_δ g I n₁ k h12, hv', hxy, sub_self]
  obtain ⟨c, hc⟩ := (hb n₁ hk1).2 (CohomologyClass.mk (Cocycle.mk _ k h12 hyc))
  obtain ⟨u, rfl⟩ := CohomologyClass.mk_surjective c
  have hpu : δ n₁ k (pre g I n₁ u) = 0 := by
    rw [← pre_δ g I n₁ k h12, Cocycle.δ_eq_zero, map_zero]
  rw [cpull_mk_eq_mk_of_pre g n₁ u (Cocycle.mk (pre g I n₁ u) k h12 hpu) rfl, mk_eq_mk_iff _ _ n₀ h01] at hc
  obtain ⟨w, hw⟩ := hc
  simp only [Cocycle.mk_coe] at hw
  refine ⟨v' + u, -w, ?_, ?_⟩
  · rw [δ_add, hv', Cocycle.δ_eq_zero, add_zero]
  · rw [map_add, δ_neg, hw]
    abel

private theorem conn_of_coneAt {K L I : Cx R} (g : K ⟶ L) (M : ℤ)
    (h : ∀ k ≤ M, ConeAt (dC L I) (dC K I) (pre g I) k) :
    (∀ n, n < M → Function.Bijective (cpull g I n)) ∧ Function.Injective (cpull g I M) := by
  have inj : ∀ n, n ≤ M → Function.Injective (cpull g I n) := by
    intro n hn
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective c
    have hpx : δ n (n + 1) (pre g I n x) = 0 := by
      rw [← pre_δ g I n (n + 1) rfl, Cocycle.δ_eq_zero, map_zero]
    rw [cpull_mk_eq_mk_of_pre g n x (Cocycle.mk _ (n + 1) rfl hpx) rfl, ← CohomologyClass.mk_zero,
      mk_eq_mk_iff _ _ (n - 1) (by ring)] at hc
    obtain ⟨y, hy⟩ := hc
    simp only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hy
    obtain ⟨v, w, hv, -⟩ := h n hn (n - 1 - 1) (n - 1) (n + 1) (by ring) (by ring) rfl
      (x : Cochain L I n) y (Cocycle.δ_eq_zero x _) (by simp only [dC, AddMonoidHom.mk'_apply, hy])
    rw [← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ (n - 1) (by ring)]
    simp only [dC, AddMonoidHom.mk'_apply] at hv
    exact ⟨v, by rw [← hv]; simp⟩
  refine ⟨fun n hn => ⟨inj n hn.le, ?_⟩, inj M le_rfl⟩
  intro c
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨v, w, hv, hw⟩ := h (n + 1) (by omega) (n - 1) n (n + 1 + 1) (by ring) rfl rfl 0
    (z : Cochain K I n) (map_zero _) (by simp [dC, Cocycle.δ_eq_zero])
  simp only [dC, AddMonoidHom.mk'_apply] at hv hw
  have hvδ : δ n (n + 1) v = 0 := hv.symm
  have hpv : δ n (n + 1) (pre g I n v) = 0 := by
    rw [← pre_δ g I n (n + 1) rfl, hvδ, map_zero]
  refine ⟨CohomologyClass.mk (Cocycle.mk v (n + 1) rfl hvδ), ?_⟩
  rw [cpull_mk_eq_mk_of_pre g n _ (Cocycle.mk (pre g I n v) (n + 1) rfl hpv) rfl,
    mk_eq_mk_iff _ _ (n - 1) (by ring)]
  refine ⟨-w, ?_⟩
  simp only [Cocycle.mk_coe, δ_neg, hw]
  abel

end Classes

end UpperTheory.TruncCx

private theorem ιTerm_comp_f_naturality {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (c k t : ℤ)
    (h : c + k = t) :
    GlobalTheory.ColFilt.ιTerm K c k t h ≫ g.f t =
      ((CochainComplex.singleFunctor (Shv R) 0).map (g.f c)).f k ≫ GlobalTheory.ColFilt.ιTerm L c k t h := by
  by_cases hk : k = 0
  · subst hk
    have hct : t = c := by omega
    subst hct
    rw [GlobalTheory.ColFilt.ιTerm_zero, GlobalTheory.ColFilt.ιTerm_zero]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self]
  · rw [GlobalTheory.ColFilt.ιTerm_ne K c k t h hk, GlobalTheory.ColFilt.ιTerm_ne L c k t h hk]
    simp

open GlobalTheory.ColFilt UpperTheory.TruncCx in
theorem UpperTheory.cochainPullback_bijective_of_termwise_bijective_injective :
    ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) → ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ), (∀ p : ℤ, (∀ n, n < m + p → Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) ∧ Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I (m + p))) → (∀ n, n < m → Function.Bijective (cpull g I n)) ∧ Function.Injective (cpull g I m) := by
  intro R _ I _ _ K L _ _ g m hyp
  apply UpperTheory.TruncCx.conn_of_coneAt g m
  intro k hk
  refine UpperTheory.TruncCx.coneAt_of_graded ((isColumns_terms L).isFilt I) ((isColumns_terms K).isFilt I)
    (UpperTheory.TruncCx.pre g I) (fun n m' h x => UpperTheory.TruncCx.pre_δ g I n m' h x) ?_
    (fun p => UpperTheory.TruncCx.pre ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I) ?_ m
    (fun p _ k' hk' => UpperTheory.TruncCx.coneAt_of_conn _ (m + p) (hyp p).1 (hyp p).2 k' hk') k hk
  · intro p n x hx c k' t h q hq hpc
    have hx' : ∀ (c k t : ℤ) (h : c + k = t) (q : ℤ) (hq : t + n = q), p < c →
        ιTerm L c k t h ≫ x.v t q hq = 0 := hx
    rw [UpperTheory.TruncCx.pre_v, ← Category.assoc, ιTerm_comp_f_naturality, Category.assoc,
      hx' c k' t h q hq hpc, comp_zero]
  · intro p n m' h x _
    refine Cochain.ext _ _ (fun k' q hq => ?_)
    rw [UpperTheory.TruncCx.pre_v, restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega),
      restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega), UpperTheory.TruncCx.pre_v,
      ← Category.assoc, ← Category.assoc, ιTerm_comp_f_naturality]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ContinuousSectionsBijectiveAdditiveNatural
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

private theorem cPre_isSheaf (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [ContinuousConstSMul R T] :
    Presheaf.IsSheaf Scheme.proetaleTopology.{0} (cPre R T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
    isSheaf_iff_isSheaf_of_type]
  have h := Presieve.isSheaf_of_le _ Scheme.proetaleTopology_le_fpqcTopology
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqcTopology_continuousMapPresheaf.{0, 0} T))
  have h' : Presieve.IsSheaf Scheme.proetaleTopology
      (continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1}) :=
    (Presieve.isSheaf_comp_uliftFunctor_iff _).2 h
  exact Presieve.isSheaf_iso _
    (NatIso.ofComponents (fun U => Iso.refl _) (by intros; rfl) :
      continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1} ≅ cPre R T ⋙ forget _) h'

theorem UpperTheory.continuousSections_bijective_additive_natural :
    ∀ (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (U : Scheme.{0}),
    Function.Bijective (cSec R T (U := U)) ∧ (∀ a b : C(U, T), cSec R T (a + b) = cSec R T a + cSec R T b) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ U) (a : C(U, T)), rs _ g (cSec R T a) = cSec R T (a.comp g.base.hom)) ∧
    ∀ (T' : Type) [AddCommGroup T'] [Module R T'] [TopologicalSpace T'] [IsTopologicalAddGroup T'] [ContinuousConstSMul R T'] (u : T →L[R] T') (a : C(U, T)), ap (cMap u).hom (cSec R T a) = cSec R T' ((⟨u, u.continuous⟩ : C(T, T')).comp a) := by
  intro R _ T _ _ _ _ _ U
  haveI : IsIso (toSheafify Scheme.proetaleTopology (cPre R T)) :=
    isIso_toSheafify _ (cPre_isSheaf R T)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hb := ConcreteCategory.bijective_of_isIso
      ((toSheafify Scheme.proetaleTopology (cPre R T)).app (op U))
    exact hb.comp Equiv.ulift.symm.bijective
  · intro a b
    exact map_add (ModuleCat.Hom.hom ((toSheafify Scheme.proetaleTopology (cPre R T)).app (op U)))
      (ULift.up a) (ULift.up b)
  · intro V g a
    exact (congrArg (fun f => ModuleCat.Hom.hom f (ULift.up a))
      ((toSheafify Scheme.proetaleTopology (cPre R T)).naturality g.op)).symm
  · intro T' _ _ _ _ _ u a
    exact congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) (ULift.up a))
      (toSheafify_naturality Scheme.proetaleTopology (cPreMap u)).symm
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyIsUnitOrIsUnitOfSpanPairEqTop
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private theorem unit_on_basicOpen (T : Scheme.{0}) (a : Γ(T, ⊤)) :
    IsUnit ((T.basicOpen a).ι.appTop.hom a) := by
  have hb := Scheme.Opens.ι_preimage_self (T.basicOpen a)
  rw [Scheme.preimage_basicOpen] at hb
  apply RingedSpace.isUnit_of_isUnit_germ _ ⊤
  intro x hx
  have hx' : x ∈ (T.basicOpen a).toScheme.basicOpen
      ((ConcreteCategory.hom ((T.basicOpen a).ι.app ⊤)) a) := by
    rw [hb]
    trivial
  exact (Scheme.mem_basicOpen _ _ x hx).mp hx'

private theorem mem_basicOpen_or (T : Scheme.{0}) (a b : Γ(T, ⊤)) (h : Ideal.span {a, b} = ⊤) (u : T) :
    u ∈ T.basicOpen a ∨ u ∈ T.basicOpen b := by
  have h1 : (1 : Γ(T, ⊤)) ∈ Ideal.span {a, b} := h ▸ Submodule.mem_top
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp h1
  have hu : IsUnit (ConcreteCategory.hom (T.presheaf.germ ⊤ u trivial) (x * a) +
      ConcreteCategory.hom (T.presheaf.germ ⊤ u trivial) (y * b)) := by
    rw [← map_add, hxy, map_one]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hx | hy
  · left
    rw [Scheme.mem_basicOpen_top]
    rw [map_mul] at hx
    exact isUnit_of_mul_isUnit_right hx
  · right
    rw [Scheme.mem_basicOpen_top]
    rw [map_mul] at hy
    exact isUnit_of_mul_isUnit_right hy

theorem UpperTheory.locally_isUnit_or_isUnit_of_span_pair_eq_top :
    ∀ (T : Scheme.{0}) (a b : Γ(T, ⊤)), Ideal.span {a, b} = ⊤ → Loc T fun V g => IsUnit (g.appTop.hom a) ∨ IsUnit (g.appTop.hom b) := by
  intro T a b h
  let U : Bool → T.Opens := fun i => bif i then T.basicOpen a else T.basicOpen b
  have hU : TopologicalSpace.IsOpenCover U := by
    apply eq_top_iff.mpr
    intro u _
    rcases mem_basicOpen_or T a b h u with hu | hu
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, hu⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hu⟩
  let C := T.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.ofArrows C.X C.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro V g hg
  obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  cases i
  · right
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (unit_on_basicOpen T b).map c.appTop.hom
  · left
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (unit_on_basicOpen T a).map c.appTop.hom
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplicativeGroupHomExistsUniqueOfUnit
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.GqPt

private theorem tR_zpow (q : ℕ) (n : ℤ) :
    (((tR q) ^ n : (LqR q)ˣ) : LqR q) = LaurentPolynomial.T n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T 1 : LqR q) ^ k = _
    rw [LaurentPolynomial.T_pow]; simp
  · rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T (-1) : LqR q) ^ k = _
    rw [LaurentPolynomial.T_pow]; simp

private theorem hom_ext (q : ℕ) {R : Type} [CommRing R] {f g : LqR q →+* R}
    (h : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g :=
  _root_.UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext q h

private noncomputable def sec {X : Scheme.{0}} {R : CommRingCat.{0}} (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

private theorem sec_inj {X : Scheme.{0}} {R : CommRingCat.{0}} {f g : X ⟶ Spec R} (h : sec f = sec g) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h)

private theorem sec_to {X : Scheme.{0}} {R : CommRingCat.{0}} (φ : R ⟶ Γ(X, ⊤)) :
    sec (X.toSpecΓ ≫ Spec.map φ) = φ := by
  simp only [sec, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

private theorem val_map_tq (q : ℕ) {T : Scheme.{0}} (s : T ⟶ Gq q) :
    ((Units.map s.appTop.hom.toMonoidHom (tq q) : (Γ(T, ⊤))ˣ) : Γ(T, ⊤)) =
      (sec s).hom (LaurentPolynomial.T 1) := rfl

end UpperTheory.GqPt

open UpperTheory.GqPt in
theorem UpperTheory.multiplicativeGroup_hom_existsUnique_of_unit :
    ∀ (q : ℕ) [NeZero q] (T : Scheme.{0}), IsUnit ((q : ℕ) : Γ(T, ⊤)) → ∀ t : (Γ(T, ⊤))ˣ, ∃! s : T ⟶ Gq q, Units.map s.appTop.hom.toMonoidHom (tq q) = t := by
  intro q _ T hq t
  let lam : Localization.Away (q : ℤ) →+* Γ(T, ⊤) :=
    IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom Γ(T, ⊤)) (by simpa using hq)
  let φ : LqR q →+* Γ(T, ⊤) := LaurentPolynomial.eval₂ lam t
  have hφ : φ (LaurentPolynomial.T 1) = t := by
    simp only [φ, LaurentPolynomial.eval₂_T, zpow_one]
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · refine Units.ext ?_
    rw [val_map_tq, sec_to]
    exact hφ
  · intro s hs
    refine sec_inj ?_
    rw [sec_to]
    refine CommRingCat.hom_ext (hom_ext q ?_)
    have h1 := val_map_tq q s
    rw [hs] at h1
    exact h1.symm.trans hφ.symm
end

