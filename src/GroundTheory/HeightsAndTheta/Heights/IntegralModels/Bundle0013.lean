import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueFrameP
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

theorem repr_of_eq_sum {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {b : Fin r → E} (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) {e : E} {a : Fin r → Ω} (hae : e = ∑ q, a q • b q)
    (q : Fin r) : (Module.Basis.mk hli hsp.ge).repr e q = a q := by
  have : e = ∑ q, a q • (Module.Basis.mk hli hsp.ge) q := by simpa [Module.Basis.coe_mk] using hae
  rw [this, (Module.Basis.mk hli hsp.ge).repr_sum_self a]

section FrameGlueP

variable {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}

theorem frame_at_prime {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (p : S) (hpQ : ((((p : Nat.Primes) : ℕ) : ℤ) : (chartRing ℤ x i)) ∈ Q) :
    ∃ h : Ω, ∃ hh : h ∈ (chartRing ℤ x i), (⟨h, hh⟩ : (chartRing ℤ x i)) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by
  classical
  have hPp : Prime (((p : Nat.Primes) : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (p : Nat.Primes).2
  have hnot : ∀ {s : ℤ}, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s → (s : (chartRing ℤ x i)) ∉ Q := fun hs =>
    intCast_not_mem_of_not_dvd hQ.ne_top (p : Nat.Primes).2 (by simpa using hpQ) hs
  obtain ⟨k, g, d, hg, hd, hsum, hb⟩ := (Bp p).frame i hi
  obtain ⟨t, ht, htg⟩ := exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) g hg
  obtain ⟨t', ht', htd⟩ := exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) d hd
  have hex : ∃ l, (⟨(t : Ω) * g l, htg l⟩ : (chartRing ℤ x i)) ∉ Q := by
    by_contra hall
    push Not at hall
    have hmem := mem_ideal_of_sum Q (fun l => (t' : Ω) * d l) (fun l => (t : Ω) * g l) htd htg hall
      (z := ((t' * t : ℤ) : Ω)) (intCast_mem (chartRing ℤ x i) _) (by
        have : ∑ l, (t' : Ω) * d l * ((t : Ω) * g l) = ((t' : Ω) * t) * ∑ l, d l * g l := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hsum]; push_cast; ring)
    rw [intCast_subtype] at hmem
    exact hnot (mem_primeTo.1 (mul_mem ht' ht)) hmem
  obtain ⟨l, hl⟩ := hex
  have hγA : (t : Ω) * g l ∈ (chartRing ℤ x i) := htg l
  obtain ⟨b, hli, hsp, hiff⟩ := hb l

  have hγpow : ∀ (n : ℕ) {y : Ω}, g l ^ n * y ∈ chartRing (o p) x i →
      ((t : Ω) * g l) ^ n * y ∈ chartRing (o p) x i := fun n y hy => by
    rw [mul_pow, mul_assoc]; exact mul_mem (pow_mem (intCast_mem_chartRing x i _ _) _) hy
  have hsingle : ∀ q q' : Fin r, ∃ n : ℕ, g l ^ n * (Pi.single q (1 : Ω) : Fin r → Ω) q' ∈
      chartRing (o p) x i := fun q q' => ⟨0, by
    rw [pow_zero, one_mul]
    by_cases h : q' = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _⟩

  obtain ⟨σ₁, hσ₁, n₁, hC1⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ, ∀ q, ∀ n' ≥ n,
      ((σ : Ω) * ((t : Ω) * g l) ^ n') • b q ∈ glueLat B₀ Bp i := by
    refine exists_uniform_mul _ (chartRing ℤ x i) (glueLat B₀ Bp i) (glueLat_stable i) hγA b fun q => ?_
    obtain ⟨n, hn⟩ := (hiff (b q)).2 ⟨Pi.single q 1, hsingle q, by simp [Pi.single_apply]⟩
    have hγn : ((t : Ω) * g l) ^ n • b q ∈ (Bp p).lat i := by
      rw [mul_pow, mul_smul]
      exact smul_mem_of_chart (Bp p) (pow_mem (intCast_mem_chartRing x i _ _) _) hn
    obtain ⟨s, hs, hsm⟩ := (mem_Bp_iff hSR p _).1 hγn
    refine ⟨s, mem_primeTo.2 hs, n, ?_⟩
    rw [← Int.cast_smul_eq_zsmul Ω, smul_smul] at hsm
    exact hsm
  let bb := Module.Basis.mk hli hsp.ge
  have hbb : ∀ q, bb q = b q := fun q => by simp [bb, Module.Basis.coe_mk]

  obtain ⟨K₀, Gn, hG, hGspan⟩ := chartBundle_exists_gens B₀ hi

  obtain ⟨σ₂, hσ₂, n₂, hC2⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ,
      ∀ jq : (Fin K₀ × Fin r) × Fin r, ∀ n' ≥ n,
        ((σ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n') • bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i).toSubring.toAddSubgroup := by
    refine exists_uniform_mul (E := Ω) _ (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup
      (fun a ha e he => show a * e ∈ (chartRing ℤ x i) from mul_mem ha he)
      (mul_mem (intCast_mem (chartRing ℤ x i) _) hγA) _ fun jq => ?_
    obtain ⟨v, hv⟩ := exists_prime_pow_smul_mem p (hSR p) (hG jq.1)
    obtain ⟨a, ha, hae⟩ := (hiff (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v • Gn jq.1)).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
    have hq : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v * bb.repr (Gn jq.1) jq.2 = a jq.2 := by
      have := repr_of_eq_sum hli hsp hae jq.2
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at this
      exact this
    obtain ⟨n, hn⟩ := ha jq.2
    obtain ⟨s, hs, hsA⟩ := exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)
    refine ⟨s, hs, v + n, ?_⟩
    show (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i)
    have : (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 =
        (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ n * ((t : Ω) * g l) ^ v) * ((s : Ω) * (((t : Ω) * g l) ^ n * a jq.2)) := by
      rw [← hq]; ring
    rw [this]
    exact mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _) (pow_mem hγA _)) hsA
  have hσ : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) := by
    rw [hPp.dvd_mul, hPp.dvd_mul]
    rintro ((h | h) | h)
    · exact mem_primeTo.1 hσ₁ h
    · exact mem_primeTo.1 hσ₂ h
    · exact not_dvd_primeProdErase _ h
  have hmPμ : ((primeProd S : ℤ) : Ω) = ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) := by
    rw [primeProd_eq_mul p.2, Int.cast_mul]
  have hhA : ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) ∈ (chartRing ℤ x i) :=
    mul_mem (intCast_mem (chartRing ℤ x i) _) hγA

  have hC3 : ∀ e ∈ glueLat B₀ Bp i, ∀ q, ∃ n : ℕ,
      (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n * bb.repr e q ∈ (chartRing ℤ x i) := by
    intro e he q
    obtain ⟨he0, hep⟩ := (mem_glueLat B₀ Bp).1 he
    obtain ⟨a, ha, hae⟩ := (hiff e).1 ⟨0, by simpa using hep p⟩
    have hra : bb.repr e q = a q := repr_of_eq_sum hli hsp hae q
    obtain ⟨n, hn⟩ := ha q
    obtain ⟨se, hse, hseA⟩ := exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)
    obtain ⟨β, hβ, heβ⟩ := hGspan e he0
    obtain ⟨t₀, ht₀, ht₀β⟩ :=
      exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers (primeProd S)) β hβ
    obtain ⟨κ, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht₀
    have hrepr_e : bb.repr e q = ∑ j, β j * bb.repr (Gn j) q := by
      conv_lhs => rw [heβ]
      simp [map_sum, map_smul]
    have hii : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q) ∈ (chartRing ℤ x i) := by
      rw [hrepr_e, Finset.mul_sum, Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      have h1 : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q ∈ (chartRing ℤ x i) := hC2 (j, q) n₂ le_rfl
      have h2 := ht₀β j
      have : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * (β j * bb.repr (Gn j) q)) =
          ((((primeProd S) ^ κ : ℤ) : Ω) * β j) *
            ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q) := by
        rw [Int.cast_pow]; ring
      rw [this]
      exact mul_mem h2 h1
    have hc1 : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) *
        ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i) := by
      have : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) =
          ((t : Ω) * g l) ^ n * ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q)) := by
        rw [hmPμ]; ring
      rw [this]
      exact mul_mem (pow_mem hγA _) hii
    have hc2 : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i) := by
      have : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) =
          ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ n₂) * ((se : Ω) * (((t : Ω) * g l) ^ n * a q)) := by
        rw [hra]; ring
      rw [this]
      exact mul_mem (mul_mem (mul_mem (intCast_mem (chartRing ℤ x i) _) (pow_mem (intCast_mem (chartRing ℤ x i) _) _))
        (pow_mem hγA _)) hseA
    have hc := mem_of_prime_pow_mul_mem (A := (chartRing ℤ x i)) (p : Nat.Primes).2 (mem_primeTo.1 hse)
      (n₂ + κ) hc1 hc2
    refine ⟨κ + n + n₂ + 1, ?_⟩
    have : (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (κ + n + n₂ + 1) *
        bb.repr e q = ((σ₁ : Ω) ^ (κ + n + n₂ + 1) * (σ₂ : Ω) ^ (κ + n + n₂) *
          ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n + n₂ + 1) * ((t : Ω) * g l) ^ (κ + 1)) *
          ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) := by
      rw [Int.cast_mul, Int.cast_mul]; ring
    rw [this]
    exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _)
      (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem hγA _)) hc

  have hhQ : (⟨_, hhA⟩ : (chartRing ℤ x i)) ∉ Q := by
    have : (⟨_, hhA⟩ : (chartRing ℤ x i)) =
        ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : (chartRing ℤ x i)) * ⟨_, hγA⟩ :=
      Subtype.ext (by simp)
    rw [this]
    intro hmem
    rcases hQ.mem_or_mem hmem with h | h
    · exact hnot hσ h
    · exact hl h
  refine ⟨_, hhA, hhQ, b, hli, hsp, fun e => ⟨fun ⟨n, hn⟩ => ?_, fun ⟨a, ha, hae⟩ => ?_⟩⟩
  · refine ⟨fun q => bb.repr e q, fun q => ?_, ?_⟩
    · obtain ⟨n', hn'⟩ := hC3 _ hn q
      refine ⟨n' + n, ?_⟩
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add] at hn'
      exact hn'
    · conv_lhs => rw [← bb.sum_repr e]
      simp only [hbb]
  · choose nq hnq using ha
    refine ⟨Finset.univ.sup nq + (n₁ + 1), ?_⟩
    rw [hae, Finset.smul_sum]
    refine sum_mem fun q _ => ?_
    set h := ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) with hh
    have hbq : h ^ (n₁ + 1) • b q ∈ glueLat B₀ Bp i := by
      have : h ^ (n₁ + 1) = ((σ₁ : Ω) ^ n₁ * ((σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n₁ + 1) *
          ((t : Ω) * g l)) * ((σ₁ : Ω) * ((t : Ω) * g l) ^ n₁) := by
        rw [hh]; push_cast; ring
      rw [this, mul_smul]
      exact glueLat_stable i _ (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _)
        (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) hγA) _ (hC1 q n₁ le_rfl)
    have haq : h ^ (Finset.univ.sup nq) * a q ∈ (chartRing ℤ x i) := by
      rw [← pow_sub_mul_pow h (Finset.le_sup (f := nq) (Finset.mem_univ q)), mul_assoc]
      exact mul_mem (pow_mem hhA _) (hnq q)
    have : h ^ (Finset.univ.sup nq + (n₁ + 1)) • (a q • b q) =
        (h ^ (Finset.univ.sup nq) * a q) • (h ^ (n₁ + 1) • b q) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]
    exact glueLat_stable i _ haq _ hbq

end FrameGlueP

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PBasisIsoFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

variable {Y : Scheme.{u}}

def globalSectionFamily (M : Y.Modules) (t : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun V => (M.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom t)
    (fun V W f => by
      change (M.presheaf.map f).hom ((M.presheaf.map _).hom t) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

def basisHom (M : Y.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤)) : freeModule Y n ⟶ M :=
  (SheafOfModules.freeHomEquiv M).symm (fun i => globalSectionFamily M (s i.down))

theorem basisHom_app_stdSection (M : Y.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤)) (i : Fin n) :
    ((basisHom M s).app ⊤).hom (stdSection Y n i) = s i := by
  have h1 : SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i) ≫ basisHom M s =
      M.unitHomEquiv.symm (globalSectionFamily M (s i)) := by
    refine (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (basisHom M s) (ULift.up i)).symm.trans ?_
    congr 1
    exact congrFun ((SheafOfModules.freeHomEquiv M).apply_symm_apply _) (ULift.up i)
  have e1 : (M.unitHomEquiv (SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i) ≫
      basisHom M s)).val (op ⊤) = (globalSectionFamily M (s i)).val (op ⊤) := by
    have := congrArg (fun φ => (M.unitHomEquiv φ).val (op ⊤)) h1
    simpa only [Equiv.apply_symm_apply] using this
  have e2 : (M.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op).hom (s i) = s i := by
    rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
    simp
  exact e1.trans (by exact e2)

theorem BasisIsoFree.proof (h : FreeSheafBasis.Statement.{u}) : BasisIsoFree.Statement.{u} := by
  intro Y M n s hs
  let ψ := basisHom M s
  have key : ∀ V : Y.Opens, (ψ.app V).hom ∘
      (fun r : Fin n → Γ(Y, V) => ∑ i, r i •
        ((freeModule Y n).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (stdSection Y n i)) =
      (fun r : Fin n → Γ(Y, V) => ∑ i, r i • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (s i)) := by
    intro V
    funext r
    simp only [Function.comp_apply, map_sum, Scheme.Modules.Hom.app_smul, app_map_apply, ψ,
      basisHom_app_stdSection]
  have hV : ∀ V : Y.Opens, IsIso (ψ.app V) := fun V =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((Function.Bijective.of_comp_iff _ (h Y n V le_top)).mp (by rw [key V]; exact hs V le_top))
  have : IsIso ψ := Scheme.Modules.Hom.isIso_iff_isIso_app.mpr hV
  exact ⟨(asIso ψ).symm⟩

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PClearDenominators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section Sheaf

variable {X : Scheme.{0}} (M : X.Modules)

lemma res_res {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C) (x : Γ(M, C)) :
    (M.presheaf.map i.op).hom ((M.presheaf.map j.op).hom x) = (M.presheaf.map k.op).hom x := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, CategoryTheory.Functor.map_comp]
  rfl

lemma modules_eq_of_locally {V : X.Opens} (a b : Γ(M, V))
    (h : ∀ x ∈ V, ∃ (W : X.Opens) (i : W ≤ V), x ∈ W ∧
      (M.presheaf.map (homOfLE i).op).hom a = (M.presheaf.map (homOfLE i).op).hom b) : a = b := by
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  choose W i hx h using h
  refine F.eq_of_locally_eq' (U := fun x : V => W x.1 x.2) V (fun x => homOfLE (i _ _)) ?_ a b
    (fun x => h _ _)
  intro x hxV
  exact Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _ _⟩

lemma modules_exists_glue {V : X.Opens} {ι : Type} (W : ι → X.Opens) (i : ∀ a, W a ≤ V)
    (hcov : ∀ x ∈ V, ∃ a, x ∈ W a) (sf : ∀ a, Γ(M, W a))
    (hsf : ∀ a b, (M.presheaf.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op).hom (sf a) =
      (M.presheaf.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op).hom (sf b)) :
    ∃ s : Γ(M, V), ∀ a, (M.presheaf.map (homOfLE (i a)).op).hom s = sf a := by
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W V (fun a => homOfLE (i a))
    (fun x hxV => Opens.mem_iSup.2 (hcov x hxV)) sf hsf
  exact ⟨s, hs⟩

variable {M}

lemma IsBasisOn.bijective_self {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) :
    Function.Bijective (fun r : Fin n → Γ(X, U) => ∑ i, r i • s i) := by
  have e : ∀ x : Γ(M, U), (M.presheaf.map (homOfLE (le_refl U)).op).hom x = x := by
    intro x
    rw [Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id, CategoryTheory.Functor.map_id]
    rfl
  simpa only [e] using hs U le_rfl

end Sheaf

section Pull

variable {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules)

lemma pullSectionOn_smul (U : Z.Opens) (r : Γ(Z, U)) (m : Γ(M, U)) :
    pullSectionOn g M U (r • m) = g.app U r • pullSectionOn g M U m :=
  Scheme.Modules.Hom.app_smul _ r m

lemma pullSectionOn_res {U V : Z.Opens} (h : V ≤ U) (i : g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ U) (m : Γ(M, U)) :
    pullSectionOn g M V ((M.presheaf.map (homOfLE h).op).hom m) =
      (((Scheme.Modules.pullback g).obj M).presheaf.map i.op).hom (pullSectionOn g M U m) := by
  have := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf.naturality
    (homOfLE h).op
  have h2 := congrArg (fun φ => φ.hom m) this
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h2
  rw [Subsingleton.elim i ((Opens.map g.base).map (homOfLE h))]
  exact h2

lemma pullSectionOn_sum (U : Z.Opens) {n : ℕ} (t : Fin n → Γ(M, U)) (r : Fin n → Γ(Z, U)) :
    pullSectionOn g M U (∑ i, r i • t i) = ∑ i, g.app U (r i) • pullSectionOn g M U (t i) := by
  rw [map_sum]
  simp only [pullSectionOn_smul]

end Pull

section Local

variable (hPB : PullbackBasis.Statement.{0}) (hRL : RatLocalAffine.Statement)
  {X : Scheme.{0}} (f : X ⟶ SpecZ) [Flat f] (L : X.Modules)
  {W : X.Opens} (hW : IsAffineOpen W) {n : ℕ} {t : Fin n → Γ(L, W)} (ht : IsBasisOn L W t)
include hPB hRL hW ht

lemma pullSectionOn_injective_of_basis :
    Function.Injective (pullSectionOn (baseChangeMap f ℚ) L W) := by
  have hb := (hPB _ _ (baseChangeMap f ℚ) L W n t ht).bijective_self
  have hinj := (hRL X f W hW).1
  rw [injective_iff_map_eq_zero]
  intro τ hτ
  obtain ⟨r, rfl⟩ := ht.bijective_self.2 τ
  have h0 : (fun i => (baseChangeMap f ℚ).app W (r i)) = 0 := by
    apply hb.1
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    exact (pullSectionOn_sum _ L W t r).symm.trans hτ
  have hr : r = 0 := funext fun i => hinj (by rw [Pi.zero_apply, map_zero]; exact congrFun h0 i)
  simp [hr]

lemma exists_pullSectionOn_eq_nsmul_of_basis
    (σ : Γ((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L, baseChangeMap f ℚ ⁻¹ᵁ W)) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : Γ(L, W), pullSectionOn (baseChangeMap f ℚ) L W τ = N • σ := by
  have hb := (hPB _ _ (baseChangeMap f ℚ) L W n t ht).bijective_self
  obtain ⟨b, rfl⟩ := hb.2 σ
  choose N hN a ha using fun i => (hRL X f W hW).2 (b i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i,
    ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • a i) • t i, ?_⟩
  rw [pullSectionOn_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, ha i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]

end Local

theorem ClearDenominators.proof (hPB : PullbackBasis.Statement.{0})
    (hRL : RatLocalAffine.Statement) : ClearDenominators.Statement := by
  classical
  intro X f _ _ _ L hL s
  have good : ∀ x : X, ∀ V : X.Opens, x ∈ V → ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ V ∧
      ∃ (n : ℕ) (t : Fin n → Γ(L, W)), IsBasisOn L W t := by
    intro x V hxV
    obtain ⟨U, -, hxU, n, t, ht⟩ := hL x
    obtain ⟨W, hW, hxW, hWle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
    exact ⟨W, hW, hxW, hWle.trans inf_le_right, n, _, ht.restrict (hWle.trans inf_le_left)⟩

  have inj : ∀ V : X.Opens, Function.Injective (pullSectionOn (baseChangeMap f ℚ) L V) := by
    intro V
    rw [injective_iff_map_eq_zero]
    intro τ hτ
    apply modules_eq_of_locally L τ 0
    intro x hx
    obtain ⟨W, hW, hxW, hWV, n, t, ht⟩ := good x V hx
    refine ⟨W, hWV, hxW, ?_⟩
    rw [map_zero]
    apply pullSectionOn_injective_of_basis hPB hRL f L hW ht
    rw [pullSectionOn_res (baseChangeMap f ℚ) L hWV (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone hWV)) τ, hτ, map_zero,
      map_zero]

  choose W hW hxW _hle n t ht using fun x : X => good x ⊤ trivial
  have hcl := fun x : X => exists_pullSectionOn_eq_nsmul_of_basis hPB hRL f L (hW x) (ht x)
    ((((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L).presheaf.map
      (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W x ≤ ⊤))).op).hom s)
  choose N hN τ hτ using hcl
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  have hcov : ∀ x : X, ∃ a : F, x ∈ W a := by
    intro x
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩

  let c : F → ℕ := fun a => ∏ y ∈ F.erase a, N y
  have hc : ∀ a : F, c a * N a = ∏ y ∈ F, N y := fun a => Finset.prod_erase_mul _ _ a.2
  let τ' : ∀ a : F, Γ(L, W a) := fun a => c a • τ a
  have hτ' : ∀ a : F, pullSectionOn (baseChangeMap f ℚ) L (W a) (τ' a) = (∏ y ∈ F, N y) •
      (((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L).presheaf.map
        (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W a ≤ ⊤))).op).hom s := by
    intro a
    simp only [τ', map_nsmul, hτ, smul_smul, hc]
  obtain ⟨T', hT'⟩ := modules_exists_glue L (V := ⊤) (fun a : F => W a) (fun _ => le_top)
    (fun x _ => hcov x) τ' (fun a b => by
      apply inj
      rw [pullSectionOn_res (baseChangeMap f ℚ) L inf_le_left (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone inf_le_left)),
        pullSectionOn_res (baseChangeMap f ℚ) L inf_le_right (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone inf_le_right)),
        hτ', hτ', map_nsmul, map_nsmul, res_res, res_res _ _ _
          (homOfLE ((Opens.map (baseChangeMap f ℚ).base).monotone (le_top : W a ⊓ W b ≤ ⊤)))])
  refine ⟨∏ y ∈ F, N y, Finset.prod_pos fun y _ => hN y, T', ?_⟩
  apply modules_eq_of_locally
  intro y _
  obtain ⟨a, ha⟩ := hcov ((baseChangeMap f ℚ).base y)
  refine ⟨(baseChangeMap f ℚ) ⁻¹ᵁ W a, (Opens.map (baseChangeMap f ℚ).base).monotone le_top, ha, ?_⟩
  rw [← pullSectionOn_top, ← pullSectionOn_res (baseChangeMap f ℚ) L le_top, hT', hτ', map_nsmul]

end

end GroundTheory.Heights₂.Heights.Model
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.IntegralModels.PDominatingDVRScheme
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open AlgebraicGeometry

theorem DominatingDVR.closed : DominatingDVR.Statement :=
  DominatingDVR.proof
    (KrullAkizuki.proof (KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.proof))
    BlowUpChart.proof

theorem not_isField_stalk_of_ne_genericPoint (Z : Scheme.{0}) [IsIntegral Z] (z : Z)
    (hz : z ≠ genericPoint Z) : ¬ IsField (Z.presheaf.stalk z) := by
  intro hF
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hmem : genericPoint Z ∈ Set.range (Z.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hgen
  obtain ⟨y, hy⟩ := hmem
  have hmax : IsLocalRing.maximalIdeal (Z.presheaf.stalk z) = ⊥ :=
    (IsLocalRing.isField_iff_maximalIdeal_eq.mp hF)
  have hyc : y = IsLocalRing.closedPoint (Z.presheaf.stalk z) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal y.isPrime.ne_top
    · exact hmax.le.trans bot_le
  apply hz
  rw [← hy, hyc, Scheme.fromSpecStalk_closedPoint]

theorem DominatingDVRScheme.proof : DominatingDVRScheme.Statement := by
  intro Z _ _ z hz
  exact DominatingDVR.closed (Z.presheaf.stalk z) (not_isField_stalk_of_ne_genericPoint Z z hz)
    Z.functionField

end GroundTheory.Heights₂.Heights.Model
end

