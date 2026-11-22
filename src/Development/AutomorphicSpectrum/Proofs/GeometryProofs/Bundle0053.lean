import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0047
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigProjMemOfFree
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.QuotEig

section Free

variable {K : Type} [Field K] {A : Subring K} {W : Type} [AddCommGroup W] [Module K W]
  {E : Type} [Field E] [NumberField E] {ρ : 𝓞 E →+* Module.End K W} {Y : Submodule A W} {N : ℕ} {t : Fin N → W}

theorem act_mem_of_free (h : HT.IsFreeOn ρ Y t) (a : 𝓞 E) {y : W} (hy : y ∈ Y) : ρ a y ∈ Y := by
  have key : Y ≤ Y.comap ((ρ a).restrictScalars A) := by
    conv_lhs => rw [h.2.2]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    change ρ a (ρ (RingOfIntegers.basis E q.2) (t q.1)) ∈ Y
    rw [← Module.End.mul_apply, ← map_mul, h.2.2,
      ← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E q.2), map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(q.1, k), rfl⟩)) _
  exact key hy

theorem eigProj_mem_of_free (h : HT.IsFreeOn ρ Y t) (σ : E →+* K) (hσ : ∀ a : E, σ a ∈ A) {y : W} (hy : y ∈ Y) :
    HT.eigProj ρ σ y ∈ Y := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  exact Y.smul_mem (⟨_, hσ (HT.dualInt E k)⟩ : A) (act_mem_of_free h _ hy)

end Free

section Main

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

theorem fst_eigProj (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (y : V × Module.Dual Ω V) :
    (HT.eigProj 𝓗.ρH σ y).1 = HT.eigProj ρ σ y.1 := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Prod.fst_sum, Prod.smul_fst, 𝓗.act_fst]

theorem mem_L_iff (𝓗 : HodgeLat L ρ bar r) (x : Cpt ξ) {z : V} :
    z ∈ L x ↔ ∃ h ∈ 𝓗.HL x, h.1 = z := by
  have e : L x = (𝓗.HL.map (LinearMap.fst Ω V (Module.Dual Ω V))) x := congrFun 𝓗.map_fst.symm x
  rw [e]
  exact Iff.rfl

end Main

theorem quot_eig : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (x : Cpt ξ), (∀ a : E, σ a ∈ regAt ξ x) → (∀ y, y ∈ 𝓗.quot σ x ↔ y ∈ 𝓗.HL x ∧ y ∈ HT.eigSp 𝓗.ρH σ) ∧ (∀ z ∈ L x, HT.eigProj ρ σ z ∈ L x) ∧ (𝓗.quot σ x).map ((LinearMap.fst Ω V (Module.Dual Ω V)).restrictScalars (regAt ξ x)) = (L.inter (HT.eigSp ρ σ)) x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ x hσ
  obtain ⟨U, hU, t, ht⟩ := 𝓗.free x
  have hfree := ht x hU
  have hstab : ∀ {h}, h ∈ 𝓗.HL x → HT.eigProj 𝓗.ρH σ h ∈ 𝓗.HL x := fun hh =>
    eigProj_mem_of_free hfree σ hσ hh
  refine ⟨fun y => ⟨?_, ?_⟩, fun z hz => ?_, ?_⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨hstab hh, HT.LatBasic.eigProj_mem _ _ _⟩
  · rintro ⟨h1, h2⟩
    exact ⟨y, h1, HT.LatBasic.eigProj_of_mem h2⟩
  · obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
    exact (mem_L_iff 𝓗 x).2 ⟨_, hstab hh, fst_eigProj 𝓗 σ h⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      have e : (HT.eigProj 𝓗.ρH σ h).1 = HT.eigProj ρ σ h.1 := fst_eigProj 𝓗 σ h
      refine ⟨(mem_L_iff 𝓗 x).2 ⟨_, hstab hh, rfl⟩, ?_⟩
      change (HT.eigProj 𝓗.ρH σ h).1 ∈ HT.eigSp ρ σ
      rw [e]
      exact HT.LatBasic.eigProj_mem _ _ _
    · rintro ⟨hz, hz'⟩
      obtain ⟨h, hh, rfl⟩ := (mem_L_iff 𝓗 x).1 hz
      refine ⟨HT.eigProj 𝓗.ρH σ h, ⟨h, hh, rfl⟩, ?_⟩
      exact (fst_eigProj 𝓗 σ h).trans (HT.LatBasic.eigProj_of_mem hz')

end GlobalTheory.CompanionTheory.Ar.Flat.QuotEig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFrameInter
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.InterFrame

theorem exists_frame_inter : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (v : Fin p → V) (x : Cpt ξ), (∀ z ∈ L x, HT.eigProj ρ σ z ∈ L x) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → (∃ (n : ℕ) (b : Fin n → V), L.IsFrameAt b x) → ∃ P : Matrix (Fin p) (Fin p) Ω, (L.inter (HT.eigSp ρ σ)).IsFrameAt (fun i => ∑ j, P i j • v j) x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p r 𝓗 σ v x hst hv hsp _
  have hrange : LinearMap.range (HT.eigProj ρ σ) = HT.eigSp ρ σ := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact HT.LatBasic.eigProj_mem ρ σ w
    · intro w hw
      exact ⟨w, HT.LatBasic.eigProj_of_mem hw⟩
  have hidem : HT.eigProj ρ σ ∘ₗ HT.eigProj ρ σ = HT.eigProj ρ σ :=
    LinearMap.ext fun w => HT.LatBasic.eigProj_of_mem (HT.LatBasic.eigProj_mem ρ σ w)
  have hVB : L.IsVBOn {x} (Module.finrank Ω V) ⊤ := fun q _ => by
    obtain ⟨U, hU, b, hb, h⟩ := 𝓗.vb q trivial
    exact ⟨U, hU, b, hb, fun q' _ hq' => h q' trivial hq'⟩
  have h := EigSplit.isVBOn_inter_range L {x} _ (HT.eigProj ρ σ) hidem hVB
    (fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hst)
  rw [hrange] at h
  obtain ⟨U, hU, f, hf, hfr⟩ := h x rfl
  have hfx := hfr x rfl hU
  have hn : Module.finrank Ω (HT.eigSp ρ σ) = p := by
    rw [← hsp, finrank_span_eq_card hv, Fintype.card_fin]
  subst hn
  have hmem : ∀ i, f i ∈ Submodule.span Ω (Set.range v) := fun i => by
    rw [hsp, ← hf]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hmem i)
  refine ⟨Matrix.of P, ?_⟩
  simpa only [Matrix.of_apply, hP] using hfx

end GlobalTheory.CompanionTheory.Ar.Flat.InterFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenOnChart
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChCoh

def IsU {Ω : Type} [Field Ω] (S : Subring Ω) (a : Ω) : Prop := a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S

section Units

variable {Ω : Type} [Field Ω] {S : Subring Ω}

theorem IsU.one : IsU S 1 := ⟨one_ne_zero, S.one_mem, by simpa using S.one_mem⟩

theorem IsU.mul {a b : Ω} (ha : IsU S a) (hb : IsU S b) : IsU S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem IsU.of_mul {a b : Ω} (ha : a ∈ S) (hb : b ∈ S) (h : IsU S (a * b)) : IsU S a := by
  have ha0 := left_ne_zero_of_mul h.1
  have hb0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact S.mul_mem hb h.2.2

theorem IsU.of_isUnit {a : S} (h : IsUnit a) : IsU S (a : Ω) := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  have hb' : (a : Ω) * (b : Ω) = 1 := by exact_mod_cast congrArg (Subtype.val) hb
  have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hb'
  refine ⟨h0, a.2, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hb']
  exact b.2

end Units

def satIdeal {A E : Type} [CommRing A] [AddCommGroup E] [Module A E] (S : Submodule A E) (f : A) (e : E) : Ideal A where
  carrier := {a | ∃ k : ℕ, (f ^ k * a) • e ∈ S}
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have : (f ^ (k + l) * (a + b)) • e = f ^ l • ((f ^ k * a) • e) + f ^ k • ((f ^ l * b) • e) := by
      simp only [smul_smul, ← add_smul]
      congr 1
      ring
    rw [this]
    exact S.add_mem (S.smul_mem _ hk) (S.smul_mem _ hl)
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (f ^ k * (c • a)) • e = c • ((f ^ k * a) • e) := by
      simp only [smul_smul, smul_eq_mul]
      congr 1
      ring
    rw [this]
    exact S.smul_mem _ hk

section Abstract

variable {A : Type} [CommRing A] {Ω : Type} [Field Ω] (ι : A →+* Ω) {E : Type} [AddCommGroup E] [Module Ω E]
  [Module A E]

theorem clear_denoms (hsm : ∀ (a : A) (e : E), a • e = ι a • e) {S : Subring Ω}
    (hfrac : ∀ a ∈ S, ∃ u v : A, IsU S (ι v) ∧ a = ι u / ι v) (s : Set E) {e : E}
    (he : e ∈ Submodule.span S s) : ∃ v : A, IsU S (ι v) ∧ v • e ∈ Submodule.span A s := by
  induction he using Submodule.span_induction with
  | mem x hx => exact ⟨1, by simpa using IsU.one, by simpa using Submodule.subset_span hx⟩
  | zero => exact ⟨1, by simpa using IsU.one, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv, h⟩ := hx
    obtain ⟨w, hw, h'⟩ := hy
    refine ⟨v * w, by rw [map_mul]; exact hv.mul hw, ?_⟩
    have : (v * w) • (x + y) = w • (v • x) + v • (w • y) := by
      simp only [smul_add, smul_smul, mul_comm]
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem _ _ h')
  | smul r x _ hx =>
    obtain ⟨v, hv, h⟩ := hx
    obtain ⟨u, w, hw, hr⟩ := hfrac r r.2
    refine ⟨w * v, by rw [map_mul]; exact hw.mul hv, ?_⟩
    have : (w * v) • (r • x) = u • (v • x) := by
      have h1 : r • x = (r : Ω) • x := rfl
      rw [h1, hsm, hsm, hsm, smul_smul, smul_smul, map_mul, hr]
      congr 1
      have := hw.1
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ h

theorem mem_of_mem_spanA (hsm : ∀ (a : A) (e : E), a • e = ι a • e) {S : Subring Ω} (hAS : ∀ a, ι a ∈ S)
    {s : Set E} {e : E} (he : e ∈ Submodule.span A s) : e ∈ Submodule.span S s := by
  induction he using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    rw [hsm]
    exact Submodule.smul_mem _ (⟨ι a, hAS a⟩ : S) hx

variable {Pt : Type} (R : Pt → Subring Ω)

theorem pow_smul_mem (hsm : ∀ (a : A) (e : E), a • e = ι a • e) (hAR : ∀ q a, ι a ∈ R q)
    (hfrac : ∀ q, ∀ a ∈ R q, ∃ u v : A, IsU (R q) (ι v) ∧ a = ι u / ι v)
    (hprime : ∀ P : Ideal A, P.IsPrime → ∃ q : Pt, ∀ u : A, u ∈ P ↔ ¬ IsU (R q) (ι u))
    (L : ∀ q, Submodule (R q) E) {f g : A} {s t : Set E}
    (hf : ∀ q, IsU (R q) (ι f) → L q = Submodule.span (R q) s)
    (hg : ∀ q, IsU (R q) (ι g) → L q = Submodule.span (R q) t) {e : E} (he : e ∈ s) :
    ∃ m : ℕ, ∀ q, IsU (R q) (ι g) → (ι f) ^ m • e ∈ L q := by
  have hrad : g * f ∈ (satIdeal (Submodule.span A t) g e).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hn
    obtain ⟨q, hq⟩ := hprime P hP
    have hgf : IsU (R q) (ι g * ι f) := by
      rw [← map_mul]
      exact not_not.1 fun h => hn ((hq _).2 h)
    have hg' : IsU (R q) (ι g) := IsU.of_mul (hAR q g) (hAR q f) hgf
    have hf' : IsU (R q) (ι f) := IsU.of_mul (hAR q f) (hAR q g) (by rwa [mul_comm])
    have hmem : e ∈ Submodule.span (R q) t := by
      rw [← hg q hg', hf q hf']
      exact Submodule.subset_span he
    obtain ⟨v, hv, hve⟩ := clear_denoms ι hsm (hfrac q) t hmem
    have hvJ : v ∈ satIdeal (Submodule.span A t) g e := ⟨0, by simpa using hve⟩
    exact (hq v).1 (hJP hvJ) hv
  obtain ⟨m, k, hk⟩ := hrad
  refine ⟨m, fun q hgq => ?_⟩
  rw [hg q hgq]
  have h1 := mem_of_mem_spanA ι hsm (hAR q) hk
  rw [hsm] at h1
  have h2 : (ι f) ^ m • e = ((ι g ^ (k + m))⁻¹) • (ι (g ^ k * (g * f) ^ m) • e) := by
    rw [smul_smul]
    congr 1
    have := hgq.1
    simp only [map_mul, map_pow, mul_pow, pow_add]
    field_simp
  rw [h2]
  exact Submodule.smul_mem _ (⟨(ι g ^ (k + m))⁻¹, by rw [← inv_pow]; exact pow_mem hgq.2.2 _⟩ : R q) h1

theorem finite_gen (hsm : ∀ (a : A) (e : E), a • e = ι a • e) (hAR : ∀ q a, ι a ∈ R q)
    (hfrac : ∀ q, ∀ a ∈ R q, ∃ u v : A, IsU (R q) (ι v) ∧ a = ι u / ι v)
    (hprime : ∀ P : Ideal A, P.IsPrime → ∃ q : Pt, ∀ u : A, u ∈ P ↔ ¬ IsU (R q) (ι u))
    (hloc : ∀ q, IsLocalRing (R q)) (L : ∀ q, Submodule (R q) E)
    (hcover : ∀ p : Pt, ∃ (f : A) (n : ℕ) (b : Fin n → E), IsU (R p) (ι f) ∧
      ∀ q, IsU (R q) (ι f) → L q = Submodule.span (R q) (Set.range b)) :
    ∃ (n : ℕ) (b : Fin n → E), ∀ q, L q = Submodule.span (R q) (Set.range b) := by
  choose F n b hF hL using hcover
  have htop : Ideal.span (Set.range F) = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨q, hq⟩ := hprime P hP.isPrime
    exact (hq (F q)).1 (hle (Ideal.subset_span ⟨q, rfl⟩)) (hF q)
  have h1 : (1 : A) ∈ Ideal.span (Set.range F) := by rw [htop]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1
  have hsome : ∀ q, ∃ l ∈ c.support, IsU (R q) (ι (F l)) := by
    intro q
    by_contra hn
    push_neg at hn
    letI := hloc q
    let φ : A →+* R q := ι.codRestrict (R q) (hAR q)
    have hmem : (1 : A) ∈ (IsLocalRing.maximalIdeal (R q)).comap φ := by
      rw [← hc]
      refine Ideal.sum_mem _ fun l hl => Ideal.mul_mem_left _ _ ?_
      show φ (F l) ∈ IsLocalRing.maximalIdeal (R q)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hn l hl (IsU.of_isUnit hu)
    have h1' : (1 : R q) ∈ IsLocalRing.maximalIdeal (R q) := by simpa using hmem
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1'
  have hm : ∀ (l : Pt) (i : Fin (n l)), ∃ m : ℕ, ∀ q, (ι (F l)) ^ m • b l i ∈ L q := by
    intro l i
    have h := fun j => pow_smul_mem ι R hsm hAR hfrac hprime L (f := F l) (g := F j) (hL l) (hL j)
      (e := b l i) ⟨i, rfl⟩
    choose m hm using h
    refine ⟨c.support.sup m, fun q => ?_⟩
    obtain ⟨j, hj, hu⟩ := hsome q
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) hj)
    rw [hd, add_comm, pow_add, mul_smul]
    exact (L q).smul_mem (⟨(ι (F l)) ^ d, pow_mem (hAR q _) _⟩ : R q) (hm j q hu)
  choose m hm using hm
  let g : (Σ l : c.support, Fin (n l)) → E := fun t => (ι (F t.1)) ^ (m t.1 t.2) • b t.1 t.2
  let eq := Fintype.equivFin (Σ l : c.support, Fin (n l))
  refine ⟨_, g ∘ eq.symm, fun q => ?_⟩
  rw [EquivLike.range_comp]
  apply le_antisymm
  · obtain ⟨l, hl, hu⟩ := hsome q
    rw [hL l q hu, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : b l i = ((ι (F l))⁻¹) ^ (m l i) • g ⟨⟨l, hl⟩, i⟩ := by
      show _ = _ • (ι (F l)) ^ (m l i) • b l i
      rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hu.1, one_pow, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ (⟨_, pow_mem hu.2.2 _⟩ : R q) (Submodule.subset_span ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hm _ _ q

end Abstract

theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  unfold regAt
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (RingHom.rangeRestrict_surjective _)

end GlobalTheory.CompanionTheory.Ar.ChCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_normalized_minors : ∀ {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin r) (I : Fin k → Fin r), NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I → ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f)) → (∀ (k : ℕ) (hk : k ≤ r), ∃ I : Fin k → Fin r, NormAt O Y k hk I) → ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueDominatingMap
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.ChMorph

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem hom_eq_of_points {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) {i : Ω →+* Ω'} {f g : X' ⟶ X}
    (hf : Dominates ξ' ξ f i) (hg : Dominates ξ' ξ g i) (hb : ∀ q, f q = g q) : f = g := by
  have hbase : f.base = g.base := by
    ext q
    exact hb q
  refine Scheme.Hom.ext hbase fun U => ?_
  ext s
  refine TopCat.Presheaf.section_ext X'.sheaf _ _ _ fun q hq => ?_
  have hqg : g q ∈ U := hq
  have hqf : f q ∈ U := by rw [hb q]; exact hqg
  have hpf : genPt ξ ⤳ f q := RegAtDom.map_genPt hf ▸ (hall q).map f.continuous
  have hpg : genPt ξ ⤳ g q := RegAtDom.map_genPt hg ▸ (hall q).map g.continuous
  have key : ∀ (a b : X) (_ : a = b) (ha : genPt ξ ⤳ a) (hb : genPt ξ ⤳ b) (h1 : a ∈ U) (h2 : b ∈ U),
      genMap ξ ⟨a, ha⟩ ((X.presheaf.germ U a h1).hom s) = genMap ξ ⟨b, hb⟩ ((X.presheaf.germ U b h2).hom s) := by
    rintro a _ rfl ha hb h1 h2
    rfl
  apply hgen.inj ⟨q, hall q⟩
  have e1 := RegAtDom.genMap_stalkMap hf q (hall q) hpf ((X.presheaf.germ U (f q) hqf).hom s)
  have e2 := RegAtDom.genMap_stalkMap hg q (hall q) hpg ((X.presheaf.germ U (g q) hqg).hom s)
  rw [Scheme.Hom.germ_stalkMap_apply] at e1 e2
  have e3 := key _ _ (hb q) hpf hpg hqf hqg
  rw [← e3, ← e1] at e2
  refine (congrArg (genMap ξ' ⟨q, hall q⟩) ?_).trans e2.symm
  exact TopCat.Presheaf.germ_res_apply X'.presheaf _ q hqg _

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  {o' : Type} [CommRing o'] [Algebra o' Ω'] {κ' : Type} {y : κ' → Ω'}

theorem specializes_of_dominates (M : PModel o x) (M' : PModel o' y) {i : Ω →+* Ω'} {f g : M'.X ⟶ M.X}
    (hf : Dominates M'.ξ M.ξ f i) (hg : Dominates M'.ξ M.ξ g i) (q : M'.X) : g q ⤳ f q := by
  let p' : Cpt M'.ξ := ⟨q, M'.all q⟩
  obtain ⟨h1, fa, -⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ f i hf p'
  obtain ⟨h2, ga, gb⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ g i hg p'
  replace gb := gb M'.tie.gen
  obtain ⟨c, hc0, hc⟩ := M.tie.cover ⟨f q, h1⟩
  obtain ⟨c', hc'0, hc'⟩ := M.tie.cover ⟨g q, h2⟩
  have hu : unitAt M.ξ ⟨g q, h2⟩ (x c / x c') := by
    refine gb _ (hc' c) ⟨?_, ga _ (hc' c), ?_⟩
    · exact (map_ne_zero i).2 (div_ne_zero hc0 hc'0)
    · rw [← map_inv₀, inv_div]
      exact fa _ (hc c')
  have hin : InChart M.ξ x c ⟨g q, h2⟩ := by
    refine ⟨hc0, fun j => ?_⟩
    have : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (hc' j) hu.2.2
  refine specializes_iff_forall_open.2 fun V hV hq => ?_
  obtain ⟨a, ha, hau, hU⟩ := GlobalTheory.T.chart_unit_basic_open o Ω κ x M c ⟨f q, h1⟩ ⟨V, hV⟩ ⟨hc0, hc⟩ hq
  have hag : a ∈ regAt M.ξ ⟨g q, h2⟩ := (M.tie.ring c hc0 a).1 ha _ hin
  refine hU ⟨g q, h2⟩ hin (gb a hag ⟨(map_ne_zero i).2 hau.1, fa a hau.2.1, ?_⟩)
  rw [← map_inv₀]
  exact fa _ hau.2.2

theorem existsUnique_dominates :
    ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x)
      (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω')
      (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) →
      ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M o' _ Ω' _ _ κ' _ y M' i h
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular M.X Ω M.ξ o κ x M'.X Ω' M'.ξ i M.tie M'.tie.gen M'.all
    (fun r p' => by
      obtain ⟨c, -, H⟩ := h p'
      exact H _ (Subalgebra.algebraMap_mem _ r))
    (fun p' => by
      obtain ⟨c, hc, H⟩ := h p'
      refine ⟨c, (map_ne_zero i).2 hc, fun c' => ?_⟩
      rw [← map_div₀]
      exact H _ (Algebra.subset_adjoin ⟨c', rfl⟩))
  refine ⟨f, hf, fun g hg => ?_⟩
  exact hom_eq_of_points M'.tie.gen M'.all hg hf fun q =>
    ((specializes_of_dominates M M' hf hg q).antisymm (specializes_of_dominates M M' hg hf q)).eq

end GlobalTheory.CompanionTheory.Ar.ChMorph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreCurveDegreeCompare
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fibreCurve_curveIn_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) :=
  @PositivityTheory.Xgn.exists_curve_in_fibre_degree

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GreenCurrentIntegralFormulaStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.green_current_integral_formula : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ), OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ z, PtOver y φ σ z → u z = t σ) → (∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) → ptsIntegral W (pot L) u = ∑ σ : F →+* ℂ, t σ * ptsIntegral W (pot L) (χ σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_place | exact GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_place | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_place <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualActionCompatStatement
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_chart_dual_action_compat : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (m : ℕ), Module.Projective A (D.omHT σ) → (∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y') → ∃ Rr : (Fin N → K) →ₗ[K] Li, (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) 1 (algebraMap A K).range, Rr (fun l => D.h (Pi.single l 1) e) = e + ((p : K) ^ m) • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_retraction_mod | exact GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_retraction_mod | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_retraction_mod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeSpanIndependent
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem HodgeLat.quot_det_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (u : Fin r → V × Module.Dual Ω V), (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) ∧ (detLat (𝓗.quot σ) u).IsVB 1 ⊤ ∧ ∀ (p : Cpt ξ) (A : Matrix (Fin r) (Fin r) Ω), (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) p → (detLat (𝓗.quot σ) u).IsGenAt p A.det := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ u hσ hu hspan
  have hvb : (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) := by
    intro p _
    obtain ⟨U, hpU, x, hx⟩ := 𝓗.free p
    refine ⟨U, hpU, fun i => HT.eigProj 𝓗.ρH σ (x i), HodgeDeterminantLattice.span_eigProj σ (hx p hpU), ?_⟩
    intro q _ hq
    refine ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ (hx q hq), ?_⟩
    rw [HodgeLat.quot_apply]
    exact HodgeDeterminantLattice.eigQuot_eq_span σ (hx q hq) (fun a => ⟨⟨σ a, hσ q a⟩, rfl⟩)
  exact ⟨hvb, HodgeDeterminantLattice.detLat_isVB hvb hu hspan, fun p A hA => HodgeDeterminantLattice.detLat_of_frame hu hA⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartDualActionStatement
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_dual_action : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → ∃ (J : Li →ₗ[K] (Fin N → K)) (Rr : (Fin N → K) →ₗ[K] Li), (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e) ∧ ∀ l, J e l = algebraMap A K (i f l)) ∧ (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, Rr (J e) = e + ((p : K) ^ m) • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_lift_retract | exact GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_lift_retract | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HTL.exists_lift_retract <;> assumption)
end

