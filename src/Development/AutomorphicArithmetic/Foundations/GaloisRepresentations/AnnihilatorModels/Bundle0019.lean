import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsogComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem comp_pow' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) : f ≫ (g ^ n) = (f ≫ g) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Hom.one_def]
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y) (toUnit X)]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem pow_comp' {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y Z : C} [MonObj Y] [MonObj Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsMonHom g] (n : ℕ) : (f ^ n) ≫ g = (f ≫ g) ^ n := by
  exact map_pow (IsMonHom.monoidHom g X) f n

theorem UpperTheory.Gal.crystallineComparison.Mod.isogComp_of :
    PairCalc → IsogComp := by
  intro hP p _ D R _ b N S s c c' o o₁ o₂ ψ χ h1 h2
  obtain ⟨⟨k, rfl⟩, hψ, ha, he, hL, ψ', hψ', hψ1, hψ2⟩ := h1
  obtain ⟨⟨k', rfl⟩, hχ, ha', he', hL', χ', hχ', hχ1, hχ2⟩ := h2
  haveI := hψ
  haveI := hχ
  haveI := hψ'
  haveI := hχ'
  refine ⟨⟨k + k', (pow_add p k k').symm⟩, inferInstance, ?_, ?_, ?_, ⟨χ' ≫ ψ', inferInstance, ?_, ?_⟩⟩
  · intro a
    rw [← Category.assoc, ha, Category.assoc, ha', Category.assoc]
  · intro x
    rw [he', he, Category.assoc]
  · rw [(hP p D R b N S s o).2.2.2.2 o₂ (ψ ≫ χ) (p ^ k * p ^ k')]
    intro T x y
    have e1 := ((hP p D R b N S s o).2.2.2.2 o₁ ψ (p ^ k)).1 hL
    have e2 := ((hP p D R b N S s o₁).2.2.2.2 o₂ χ (p ^ k')).1 hL'
    rw [← Category.assoc, ← Category.assoc, e2, e1, mul_comm, mul_smul]
  · rw [Category.assoc, ← Category.assoc χ, hχ1, pow_comp', Category.id_comp, comp_pow', hψ1,
      ← pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ', hψ2, pow_comp', Category.id_comp, comp_pow', hχ2,
      ← pow_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKerFromU
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

section Helpers
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem cpow {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (h : T ⟶ A) (n : ℕ) :
    f ≫ (h ^ n) = (f ≫ h) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Hom.one_def]
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem powc {A B T : Over S} [GrpObj A] [GrpObj B] (h : T ⟶ A) (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    (h ^ n) ≫ f = (h ≫ f) ^ n := by
  exact map_pow (IsMonHom.monoidHom f T) h n

private abbrev sc (o : Obj b N s) (x : 𝓞 D.F) : o.A ⟶ o.A := o.act.act (algebraMap (𝓞 D.F) D.O x)

private instance sc_hom (o : Obj b N s) (x : 𝓞 D.F) : IsMonHom (sc o x) := o.act.hom _

private theorem sc_add (o : Obj b N s) (x y : 𝓞 D.F) : sc o (x + y) = sc o x * sc o y := by
  show o.act.act (algebraMap (𝓞 D.F) D.O (x + y)) = _
  rw [map_add]
  exact o.act.add _ _

private theorem sc_mul (o : Obj b N s) (x y : 𝓞 D.F) : sc o (x * y) = sc o y ≫ sc o x := by
  show o.act.act (algebraMap (𝓞 D.F) D.O (x * y)) = _
  rw [map_mul]
  exact o.act.mul _ _

private theorem sc_one (o : Obj b N s) : sc o 1 = 𝟙 o.A := by
  show o.act.act (algebraMap (𝓞 D.F) D.O 1) = _
  rw [map_one]
  exact o.act.one

private theorem sc_zero (o : Obj b N s) : sc o 0 = 1 := by
  have h := sc_add o 0 0
  rw [add_zero] at h
  open GrpObj in exact mul_eq_left.mp h.symm

private theorem sc_nat (o : Obj b N s) (n : ℕ) : sc o (n : 𝓞 D.F) = (𝟙 o.A) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, sc_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, sc_add, ih, sc_one, pow_succ]

private theorem sc_killed (o : Obj b N s) {T : Over S} (z : T ⟶ o.A) {c : ℕ} (hz : z ^ c = 1) (t : 𝓞 D.F) :
    z ≫ sc o (t * (c : 𝓞 D.F)) = 1 := by
  rw [sc_mul, sc_nat, ← Category.assoc, cpow, Category.comp_id, hz]
  have h := powc z (sc o t) 0
  rwa [pow_zero, pow_zero] at h

end Helpers

private theorem bar_bar {p : ℕ} [Fact p.Prime] (D : Datum p) (a : 𝓞 D.F) : D.bar (D.bar a) = a := by
  rw [RingOfIntegers.ext_iff, D.bar_eq, D.bar_eq, IsCMField.complexConj_apply_apply]

private theorem one_comp_monHom' {S : Scheme.{0}} {T A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B)
    [IsMonHom f] : (1 : T ⟶ A) ≫ f = 1 := by
  have h := powc (1 : T ⟶ A) f 0
  rwa [pow_zero, pow_zero] at h

private theorem comp_one_grpObj {S : Scheme.{0}} {X T A : Over S} [GrpObj A] (f : X ⟶ T) :
    f ≫ (1 : T ⟶ A) = 1 := by
  have h := cpow f (1 : T ⟶ A) 0
  rwa [pow_zero, pow_zero] at h

private theorem comp_mul_grpObj {S : Scheme.{0}} {T A B : Over S} [GrpObj B] (f : T ⟶ A)
    (h₁ h₂ : A ⟶ B) : f ≫ (h₁ * h₂) = (f ≫ h₁) * (f ≫ h₂) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem comp_id_pow_eq_pow {S : Scheme.{0}} {T A : Over S} [GrpObj A] (f : T ⟶ A) (n : ℕ) :
    f ≫ (𝟙 A ^ n) = f ^ n := by
  rw [cpow, Category.comp_id]

theorem UpperTheory.Gal.crystallineComparison.Mod.kerFromU_of :
    UElt → PairCalc → Adjoint → DivC → KerFromU := by
  intro hU hP hA hD p _ D R _ b N r w hw hle k _ s c o o₁ o₂ ψ₁ ψ₂ h1 h2 hiff T g hg
  have cpos := h1.pos
  obtain ⟨⟨e, rfl⟩, hm1, hl1, -, -, ψ₁', hm1', hψ₁a, hψ₁b⟩ := id h1
  obtain ⟨-, hm2, hl2, -, -, ψ₂', hm2', hψ₂a, hψ₂b⟩ := id h2
  haveI := hm1
  haveI := hm1'
  haveI := hm2
  haveI := hm2'
  obtain ⟨α, hα1, hα2, -⟩ := hU p D r w hw hle e
  have kill : ∀ {T' : Over (Sp k)} (u : T' ⟶ o.A), u ^ (p ^ e) = 1 → ∀ t : 𝓞 D.F,
      t ∈ Ideal.span {(p : 𝓞 D.F) ^ e} → u ≫ sc o t = 1 := by
    intro T' u hu t ht
    obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.mp ht
    rw [← Nat.cast_pow]
    exact sc_killed o u hu t'
  have uk : ∀ (o' : Obj b N s) (ψ : o.A ⟶ o'.A) [IsMonHom ψ],
      (∀ c', o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') → ∀ (T' : Over (Sp k)) (u : T' ⟶ o.A),
      u ≫ ψ = 1 → u ^ (p ^ e) = 1 → UKer r o ψ T' (u ≫ sc o α) := by
    intro o' ψ _ hl T' u hu hpu
    refine ⟨?_, e, ?_⟩
    · have hl' : sc o α ≫ ψ = ψ ≫ sc o' α := hl _
      rw [Category.assoc, hl', ← Category.assoc, hu, one_comp_monHom']
    · intro a ha
      show (u ≫ sc o α) ≫ sc o a = 1
      rw [Category.assoc, ← sc_mul]
      exact kill u hpu _ (hα1 a ha)
  have gpow : g ^ (p ^ e) = 1 := by
    rw [← comp_id_pow_eq_pow g (p ^ e), ← hψ₁a, ← Category.assoc, hg, one_comp_monHom']
  have dec : g = (g ≫ sc o α) * (g ≫ sc o (D.bar α)) := by
    rw [← comp_mul_grpObj, ← sc_add]
    obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.mp hα2
    have hsum : α + D.bar α = 1 + t' * ((p ^ e : ℕ) : 𝓞 D.F) := by
      rw [Nat.cast_pow, ht']
      ring
    rw [hsum, sc_add, comp_mul_grpObj, sc_one, Category.comp_id, sc_killed o g gpow t',
      _root_.mul_one]
  have hA1 : (g ≫ sc o α) ≫ ψ₂ = 1 := ((hiff T _).1 (uk o₁ ψ₁ hl1 T g hg gpow)).1
  obtain ⟨ν, hν, hνc⟩ := (hD (Sp k) o₂.A o₁.A o₂.ab (p ^ e) cpos).1 (ψ₂' ≫ sc o α ≫ ψ₁)
    inferInstance (by
      intro T' t ht
      have hu2 : (t ≫ ψ₂') ≫ ψ₂ = 1 := by
        rw [Category.assoc, hψ₂b, comp_id_pow_eq_pow, ht]
      have hu3 : (t ≫ ψ₂') ^ (p ^ e) = 1 := by
        rw [← powc, ht, one_comp_monHom']
      have h' := ((hiff T' _).2 (uk o₂ ψ₂ hl2 T' _ hu2 hu3)).1
      simpa only [Category.assoc] using h')
  haveI := hν
  have hfac : ν ≫ ψ₁' = ψ₂' ≫ sc o α := by
    refine (hD (Sp k) o₂.A o.A o₂.ab (p ^ e) cpos).2 _ _ inferInstance inferInstance ?_
    rw [← powc, hνc]
    simp only [Category.assoc, hψ₁a]
    rw [← Category.assoc, comp_id_pow_eq_pow]
  have h3 : ∀ (T' : Over (Sp k)) (x y : T' ⟶ o.A) (a : 𝓞 D.F),
      evc o.isLB (x ≫ sc o a) y = evc o.isLB x (y ≫ sc o (D.bar a)) :=
    (hP p D R b N (Sp k) s o).2.2.1
  have hB : (g ≫ sc o (D.bar α)) ≫ ψ₂ = 1 := by
    obtain ⟨e', hcop, hnd⟩ := (hP p D R b N (Sp k) s o₂).2.2.2.1
    have zc : ((g ≫ sc o (D.bar α)) ≫ ψ₂) ^ (p ^ e) = 1 := by
      rw [Category.assoc, ← powc, gpow, one_comp_monHom']
    have ze : ((g ≫ sc o (D.bar α)) ≫ ψ₂) ^ e' = 1 := by
      apply hnd
      have ad2 := (hA p D R b N k s (p ^ e) o o₂ ψ₂ ψ₂' h2 hm2' hψ₂b (o₂.A ⊗ T)
        (snd o₂.A T ≫ g ≫ sc o (D.bar α)) (fst o₂.A T)).1
      simp only [Category.assoc] at ad2 ⊢
      rw [ad2, ← Category.assoc, h3, bar_bar, Category.assoc, ← hfac, ← Category.assoc]
      have ad1 := (hA p D R b N k s (p ^ e) o o₁ ψ₁ ψ₁' h1 hm1' hψ₁b (o₂.A ⊗ T)
        (snd o₂.A T ≫ g) (fst o₂.A T ≫ ν)).1
      rw [← ad1, Category.assoc, hg, comp_one_grpObj]
      exact GlobalTheory.AbDual.IsAdditive.evc_one o₁.isLB (hP p D R b N (Sp k) s o₁).1 _
    have hgcd := pow_gcd_eq_one.2 ⟨ze, zc⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e hcop), pow_one] at hgcd
  have mm : ∀ a a' : T ⟶ o.A, (a * a') ≫ ψ₂ = (a ≫ ψ₂) * (a' ≫ ψ₂) :=
    fun a a' => (IsMonHom.monoidHom ψ₂ T).map_mul a a'
  rw [dec, mm, hA1, hB, _root_.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem pt_core {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {f : S' ⟶ S} {o o' : Obj b N s} {o₁ o₁' : Obj b N s'}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A) (ψ₁ : o₁.A ⟶ o₁'.A)
    (hsq : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (T : Over S') (g : T ⟶ o₁.A) :
    (g ≫ ψ₁ = 1 ↔ m.ptEquiv T g ≫ ψ = 1) ∧ (g = 1 ↔ m.ptEquiv T g = 1) ∧
      ∀ I : Ideal (𝓞 D.F), KilledBy o₁ I g ↔ KilledBy o I (m.ptEquiv T g) := by
  have key : m'.ptEquiv T (g ≫ ψ₁) = m.ptEquiv T g ≫ ψ := by
    apply Over.OverMorphism.ext
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, ← hsq,
      Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← key, MulEquiv.map_eq_one_iff]
  · rw [MulEquiv.map_eq_one_iff]
  · intro I
    unfold KilledBy
    refine forall_congr' fun a => imp_congr_right fun _ => ?_
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]

theorem UpperTheory.Gal.crystallineComparison.Mod.pullKer_of :
    PullKer := by
  intro p _ D R _ b N S S' s s' f o o' o₁ o₁' m m' ψ ψ₁ hsq
  refine ⟨?_, ?_⟩
  · intro T T₀ h g g₀ hg₀
    have hw : T₀.hom = eqToHom h ≫ T.hom ≫ f := by
      have e1 := Over.w g₀
      have e2 := Over.w (m.ptEquiv T g)
      rw [ObjMap.ptEquiv_left] at e2
      simp only [Category.assoc] at e2
      rw [← e1, hg₀]
      simp only [Category.assoc]
      rw [e2]
      rfl
    obtain ⟨L, ⟨⟨⟩⟩, hom⟩ := T₀
    change L = T.left at h
    subst h
    simp only [eqToHom_refl, Category.id_comp] at hw hg₀
    subst hw
    have hg : g₀ = m.ptEquiv T g := by
      apply Over.OverMorphism.ext
      rw [ObjMap.ptEquiv_left, hg₀]
    subst hg
    exact pt_core m m' ψ ψ₁ hsq T g
  · intro r w j htj k _ _ _ x
    obtain ⟨h1, h2⟩ := htj k (x ≫ f)
    have c := fun g => pt_core m m' ψ ψ₁ hsq (Over.mk x) g
    refine ⟨fun g hg he => ?_, ?_⟩
    · rw [(c g).2.2 w]
      obtain ⟨n, hn⟩ := he
      exact h1 _ ((c g).1.mp hg) ⟨n, ((c g).2.2 _).mp hn⟩
    · rw [← h2]
      exact Nat.card_congr ((m.ptEquiv (Over.mk x)).toEquiv.subtypeEquiv fun g => by
        rw [(c g).1, (c g).2.2 w]
        rfl)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPulledEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledEx_of :
    ObjTri → PullIsog → PullKer → PulledEx := by
  intro hTri hIsog hKer p _ D R _ b N hN hc M r w j c T S x σ hx o₁ m₁ y hy
  obtain ⟨m₀, htri⟩ := (hTri p D R b N hN hc S T.Y M.X σ (T.s ≫ M.s) M.s o₁ T.o M.univ y T.s).2 x hy m₁ T.ms
  have hσ : y ≫ T.s ≫ M.s = σ := by rw [← Category.assoc, hy, hx]
  obtain ⟨o', m', ψ, hisog, hsq⟩ := hIsog p D R b N T.Y S (T.s ≫ M.s) σ y hσ c T.o T.o' T.ψ T.isog o₁ m₀
  have htj := (hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ o' m₀ m' T.ψ ψ hsq).2 r w j T.tj
  exact ⟨⟨o', ψ, m₀, m', hsq, htri, hisog, htj⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameE
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.sameE_of :
    KillLocal → InfE → SameE := by
  intro hK hI p _ D R _ b N r κ _ _ s o o₁ o₂ ψ₁ ψ₂ hψ₂ hsub d hrep hcard hkill T g hg
  refine ⟨hK κ o.A o₂.A ψ₂ hψ₂ (UKer r o ψ₁) d hrep hsub hkill ?_ T g hg, hg.2⟩
  intro Λ _ _ _ ε g' hP hinf
  rw [hI κ o.A (UKer r o ψ₁) d hrep hcard Λ ε g' hP hinf]
  exact MonObj.one_comp _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameW
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isMonHom_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

private theorem pow_hom_comm {S : Scheme.{0}} {A : Over S} [GrpObj A] (h : A ⟶ A) [IsMonHom h] (n : ℕ) :
    h ≫ ((𝟙 A) ^ n) = ((𝟙 A) ^ n) ≫ h := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih =>
    simp only [pow_succ, Hom.mul_def, comp_lift_assoc, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, Category.comp_id, Category.id_comp, ih]

theorem UpperTheory.Gal.crystallineComparison.Mod.sameW_of :
    KillLocal → InfW → FrobPass → KerU → RepOfFF → TanOne → SameW := by
  intro hKL hInf hFP hKU hRep hTan
  intro p _ D R _ b N hm ha r w hw hu f κ _ _ _ β hβ o o₁ o₂ o₃ ψ₁ ψ₂ F e h1 hψ₂ h3 hF d hd hR1 hc1 hR2 hc2 hcl T g
  have hp : Nat.Prime p := Fact.out
  obtain ⟨-, hm1, hact1, -, -, ψ₁', hψ₁', h11, h12⟩ := h1
  obtain ⟨-, hm3, hact3, -, -, χ', hχ', h31, h32⟩ := h3
  haveI := hm1
  haveI := hm3
  haveI := hψ₁'
  haveI := hχ'
  haveI := hψ₂
  haveI hpow : IsMonHom ((𝟙 o.A) ^ p ^ (e + 1)) := isMonHom_pow o.A _
  have hactP : ∀ a : D.O, o.act.act a ≫ ((𝟙 o.A) ^ p ^ (e + 1)) = ((𝟙 o.A) ^ p ^ (e + 1)) ≫ o.act.act a := by
    intro a
    haveI := o.act.hom a
    exact pow_hom_comm (o.act.act a) _
  have kP := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o ((𝟙 o.A) ^ p ^ (e + 1)) (𝟙 o.A) (e + 1)
    hpow inferInstance hactP (by simp) (by simp)
  obtain ⟨d', hRP⟩ := hRep κ o.A _ kP.1
  have k1 := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o₁ ψ₁ ψ₁' (e + 1) hm1 hψ₁' hact1 h11 h12
  have k3 := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o₃ (ψ₂ ≫ F) χ' (e + 1) hm3 hχ' hact3 h31 h32
  obtain ⟨d₃, hR3⟩ := hRep κ o.A _ k3.1
  have sub1 : ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), UKer r o ψ₁ T g → UKer r o ((𝟙 o.A) ^ p ^ (e + 1)) T g := by
    intro T g hg
    refine ⟨?_, hg.2⟩
    rw [← h11, ← Category.assoc, hg.1]
    simp [Hom.one_def]
  have sub3 : ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), UKer r o (ψ₂ ≫ F) T g → UKer r o ((𝟙 o.A) ^ p ^ (e + 1)) T g := by
    intro T g hg
    refine ⟨?_, hg.2⟩
    rw [← h31, ← Category.assoc, hg.1]
    simp [Hom.one_def]
  have hI := hInf p f hp κ o.A (UKer r o ψ₁) (UKer r o ((𝟙 o.A) ^ p ^ (e + 1))) d d' hR1 k1.2.1 hc1 hd hRP sub1
    (hTan p D R b N hm ha r w hu κ β hβ o e)
  have fp := hFP p D R b N r f κ (spMap β) o o₂ ψ₂ hψ₂ d hR2 hc2
  have hF1 : (1 : 𝟙_ (Over (Sp κ)) ⟶ o₂.A) ≫ F = 1 := (hF _ 1).2 (fun _ => rfl)
  constructor
  · intro hg
    refine ⟨?_, hg.2⟩
    refine hKL κ o.A o₃.A (ψ₂ ≫ F) hm3 (UKer r o ψ₁) (p ^ f * d) hR1 k1.2.1 ?_ ?_ T g hg
    · intro g' hg'
      rw [← Category.assoc, ((hcl g').1 hg').1, hF1]
    · intro Λ _ _ _ ε g' hg' hi
      rw [← Category.assoc]
      exact (hF _ _).2 ((fp.2 Λ ε g' hg'.2 hi).2 ((hI Λ ε g' (sub1 _ _ hg') hi).1 hg'))
  · intro hg
    refine ⟨?_, hg.2⟩
    refine hKL κ o.A o₁.A ψ₁ hm1 (UKer r o (ψ₂ ≫ F)) d₃ hR3 k3.2.1 ?_ ?_ T g hg
    · intro g' hg'
      have h2 : g' ≫ ψ₂ = 1 := fp.1 (g' ≫ ψ₂) ((hF _ _).1 (by rw [Category.assoc]; exact hg'.1))
      exact ((hcl g').2 ⟨h2, hg'.2⟩).1
    · intro Λ _ _ _ ε g' hg' hi
      have hk : FrobKill p f hp (g' ≫ ψ₂) := (hF _ _).1 (by rw [Category.assoc]; exact hg'.1)
      exact ((hI Λ ε g' (sub3 _ _ hg') hi).2 ((fp.2 Λ ε g' hg'.2 hi).1 hk)).1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MWModEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private def killedSub {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (T : Over S) :
    letI := ptModuleWvs o T
    Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) :=
  letI := ptModuleWvs o T
  { carrier := {g | KilledBy o w g.toMul}
    zero_mem' := KilledBy.one o w T
    add_mem' := fun {g h} hg hh a ha => by
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg a ha, hh a ha, _root_.mul_one]
    smul_mem' := fun c g hg a ha => by
      show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg a ha,
        one_comp] }

theorem UpperTheory.Gal.crystallineComparison.Mod.wModEx_of :
    WModEx := by
  intro p _ D R _ b N S s o w T
  letI := ptModuleWvs o T
  have htor : Module.IsTorsionBySet (𝓞 D.F) (killedSub o w T) (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show (a : 𝓞 D.F) • (x : Additive (T ⟶ o.A)) = Additive.ofMul 1
    exact x.2 a a.2
  letI : Module (𝓞 D.F ⧸ w) (killedSub o w T) := htor.module
  refine ⟨⟨killedSub o w T, fun x => Additive.toMul (x : Additive (T ⟶ o.A)), ?_, ?_, ?_, ?_⟩⟩
  · intro x y h
    exact Subtype.ext (Additive.toMul.injective h)
  · intro g
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hg
      exact ⟨⟨Additive.ofMul g, hg⟩, rfl⟩
  · intro x y
    rfl
  · intro a x
    rw [Module.IsTorsionBySet.mk_smul]
    rfl
end

