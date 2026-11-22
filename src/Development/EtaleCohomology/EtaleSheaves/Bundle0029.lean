import Development.EtaleCohomology.EtaleSheaves.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.EtaleCohomology.EtaleSheaves.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.EtaleCohomology.EtaleSheaves.Bundle0015

-- bundled from Development.EtaleCohomology.EtaleSheaves.PushPf
section
noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.PushPf
open LateralTheory.E.t_E3Cut

section
variable {C D : Type} [CommRing C] [CommRing D] (v : C →+* D) (Q : Ideal D) [Q.IsPrime]

abbrev phi : C →+* D ⧸ Q := (Ideal.Quotient.mk Q).comp v

lemma phi_comp : (phi v Q).range.subtype.comp (phi v Q).rangeRestrict = phi v Q := by ext; rfl

lemma alg_of (x : D) (p : C[X]) (n : ℕ) (hn : v (p.coeff n) ∉ Q) (hp : p.eval₂ v x ∈ Q) :
    IsAlgebraic (phi v Q).range (Ideal.Quotient.mk Q x) := by
  refine ⟨p.map (phi v Q).rangeRestrict, ?_, ?_⟩
  · intro h0
    have := congrArg (fun q => q.coeff n) h0
    simp only [coeff_map, coeff_zero] at this
    apply hn
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h2 := congrArg Subtype.val this
    simpa using h2
  · rw [aeval_def, eval₂_map]
    have : (algebraMap (phi v Q).range (D ⧸ Q)).comp (phi v Q).rangeRestrict = phi v Q := phi_comp v Q
    rw [this, phi, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hp

lemma of_alg (x : D) (h : IsAlgebraic (phi v Q).range (Ideal.Quotient.mk Q x)) :
    ∃ p : C[X], (∃ n, v (p.coeff n) ∉ Q) ∧ p.eval₂ v x ∈ Q := by
  obtain ⟨q, hq0, hq⟩ := h
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective _ (phi v Q).rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simp only [ZeroMemClass.coe_zero]
    change Ideal.Quotient.mk Q (v (p.coeff n)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hall n)
  · rw [aeval_def, eval₂_map] at hq
    have : (algebraMap (phi v Q).range (D ⧸ Q)).comp (phi v Q).rangeRestrict = phi v Q := phi_comp v Q
    rw [this, phi, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hq
    exact hq
end

end LateralTheory.E.PushPf

namespace LateralTheory.E.PushPf
open LateralTheory.E.t_E3Cut TensorProduct

lemma gen {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D)
    (h : IsPushout f g u v) (T : Subring D) (hu : ∀ b, u.hom b ∈ T) (hv : ∀ c, v.hom c ∈ T) (d : D) :
    d ∈ T := by
  algebraize [f.hom, g.hom]
  have ht : IsPushout f g (CommRingCat.ofHom (S := B ⊗[A] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := B ⊗[A] C) Algebra.TensorProduct.includeRight.toRingHom) :=
    CommRingCat.isPushout_tensorProduct A B C
  set e := ht.isoIsPushout _ _ h
  have h1 : ∀ b : B, e.hom.hom (b ⊗ₜ[A] (1 : C)) = u.hom b := fun b => by
    have := congr($(ht.inl_isoIsPushout_hom _ _ h).hom b)
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have h2 : ∀ c : C, e.hom.hom ((1 : B) ⊗ₜ[A] c) = v.hom c := fun c => by
    have := congr($(ht.inr_isoIsPushout_hom _ _ h).hom c)
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hd : d = e.hom.hom (e.inv.hom d) := by
    have := congrArg (fun φ => φ.hom d) e.inv_hom_id
    simpa using this.symm
  rw [hd]
  induction (e.inv.hom d) using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact T.zero_mem
  | tmul b c =>
    have hbc : b ⊗ₜ[A] c = (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hbc, map_mul, h1, h2]
    exact T.mul_mem (hu b) (hv c)
  | add x y hx hy => rw [map_add]; exact T.add_mem hx hy

theorem Push_of : LateralTheory.E.AlgResPropsPf.Push := by
  intro A B C D f g u v h hf Q hQ d
  have hw : ∀ a, u.hom (f.hom a) = v.hom (g.hom a) := fun a => by
    have := congrArg (fun φ => φ.hom a) h.w
    simpa using this
  let S := (phi v.hom Q).range
  let T : Subring D :=
    { carrier := {x | IsAlgebraic S (Ideal.Quotient.mk Q x)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul] at *; exact ha.mul hb
      one_mem' := by simp only [Set.mem_ofPred_eq, map_one]; exact isAlgebraic_one
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at *; exact ha.add hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact isAlgebraic_zero
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_neg] at *
        have := (isAlgebraic_algebraMap (R := S) (A := D ⧸ Q) (-1)).mul ha
        simpa using this }
  have hv : ∀ c, v.hom c ∈ T := fun c => by
    refine alg_of v.hom Q (v.hom c) (X - Polynomial.C c) 1 ?_ ?_
    · simp only [coeff_sub, coeff_X_one, coeff_C, one_ne_zero, if_false, sub_zero, map_one]
      exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
    · simp [Q.zero_mem]
  have hu : ∀ b, u.hom b ∈ T := fun b => by
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap u.hom) (Ideal.comap_isPrime u.hom Q) b
    refine alg_of v.hom Q (u.hom b) (p.map g.hom) n ?_ ?_
    · rw [coeff_map, ← hw]; exact hn
    · have hc : v.hom.comp g.hom = u.hom.comp f.hom := by ext a; exact (hw a).symm
      rw [eval₂_map, hc, ← Polynomial.hom_eval₂]
      exact hp
  exact of_alg v.hom Q d (gen f g u v h T hu hv d)

end LateralTheory.E.PushPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ResBijPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ResBijPf

def TwSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

theorem res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res (g ≫ h) x = Sec.res g (Sec.res h x) := by
  simp [Sec.res]

theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

theorem sep' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem sec_empty {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} [IsEmpty U] (y z : Sec F U) : y = z :=
  sep' ⊥ (Scheme.bot_mem_grothendieckTopology U) y z (fun _ _ h => h.elim)

variable {q : ℕ} {i : ℤ}

theorem smul_mod {U : Scheme.{0}} (G : Sec (tw q i) U) (a : ℕ) : a • G = (a % q) • G := by
  have hq : q • G = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
      ext; simp
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div a q]
  rw [add_smul, mul_comm, mul_smul, hq, smul_zero, add_zero]

theorem smul_eq_of_cast {U : Scheme.{0}} (G : Sec (tw q i) U) {a b : ℕ} (h : (a : ZMod q) = b) : a • G = b • G := by
  rw [smul_mod G a, smul_mod G b, (ZMod.natCast_eq_natCast_iff' a b q).1 h]

theorem cast_of_smul_eq (hT : TwSec) [NeZero q] {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) {a b : ℕ}
    (h : a • twGen i ζ = b • twGen i ζ) : (a : ZMod q) = b := by
  rw [ZMod.natCast_eq_natCast_iff']
  rw [smul_mod _ a, smul_mod _ b] at h
  have ha := Nat.mod_lt a (NeZero.pos q)
  have hb := Nat.mod_lt b (NeZero.pos q)
  have key : ∀ x y : ℕ, x < q → y < q → x ≤ y → x • twGen i ζ = y • twGen i ζ → x = y := by
    intro x y hx hy hxy he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [add_smul] at he
    have hd : d • twGen i ζ = 0 := by
      have := congrArg (fun t => t - x • twGen i ζ) he
      simpa using this.symm
    have := (hT q i).2.2.1 U ζ d hd
    have : d = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega
  rcases le_total (a % q) (b % q) with hab | hab
  · exact key _ _ ha hb hab h
  · exact (key _ _ hb ha hab h.symm).symm

end LateralTheory.E.ResBijPf

namespace LateralTheory.E.ResBijPf
variable {q : ℕ} {i : ℤ}

theorem surj (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤))
    (s : Sec (tw q i) U) : ∃ k : ℕ, s = k • twGen i ζ := by
  obtain ⟨S, hS, hSP⟩ := (hT q i).2.1 U ζ s
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have hcov := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀
  have hgen : ∀ {V : Scheme.{0}} (g : V ⟶ U) (n : ℕ),
      n • twGen i (ζ.map g.appTop.hom) = Sec.res g (n • twGen i ζ) := by
    intro V g n
    rw [res_nsmul', (hT q i).2.2.2.1]
  have hc : ∀ j, ∃ c : ℕ, Sec.res (𝒰.f j) s = Sec.res (𝒰.f j) (c • twGen i ζ) := by
    intro j
    obtain ⟨c, hc⟩ := hSP _ _ (hle _ (𝒰.f j) (Presieve.ofArrows.mk j))
    exact ⟨c, hc.trans (hgen _ _)⟩
  choose c hc using hc
  have compat : ∀ j j' (x : 𝒰.X j) (x' : 𝒰.X j'), 𝒰.f j x = 𝒰.f j' x' → (c j : ZMod q) = c j' := by
    intro j j' x x' hx
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x x' hx
    have : Nonempty ↑(pullback (𝒰.f j) (𝒰.f j') : Scheme.{0}) := ⟨z⟩
    have e1 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s =
        Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j • twGen i ζ) := by
      rw [res_comp', hc j, ← res_comp']
    have e2 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s =
        Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j' • twGen i ζ) := by
      rw [pullback.condition, res_comp', hc j', ← res_comp']
    rw [← hgen] at e1 e2
    exact cast_of_smul_eq hT _ (e1.symm.trans e2)
  have hopen : ∀ j, IsOpen (Set.range (𝒰.f j)) := by
    intro j
    have := hcov.2 j
    exact (𝒰.f j).isOpenMap.isOpen_range
  obtain ⟨x0⟩ := (inferInstance : Nonempty U)
  obtain ⟨j0, y0, hy0⟩ := hcov.1 x0
  have claim : ∀ j (y : 𝒰.X j), (c j : ZMod q) = c j0 := by
    intro j y
    by_contra hne
    have hpc := (isPreconnected_univ (α := U))
      (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) = c j0), Set.range (𝒰.f j))
      (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) ≠ c j0), Set.range (𝒰.f j))
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j)
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j)
      (by
        intro x _
        obtain ⟨j', y', hy'⟩ := hcov.1 x
        by_cases h : (c j' : ZMod q) = c j0
        · exact Or.inl (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩)
        · exact Or.inr (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩))
      ⟨x0, trivial, Set.mem_iUnion₂.2 ⟨j0, rfl, y0, hy0⟩⟩
      ⟨𝒰.f j y, trivial, Set.mem_iUnion₂.2 ⟨j, hne, y, rfl⟩⟩
    obtain ⟨x, -, hA, hB⟩ := hpc
    obtain ⟨j1, h1, y1, hy1⟩ := Set.mem_iUnion₂.1 hA
    obtain ⟨j2, h2, y2, hy2⟩ := Set.mem_iUnion₂.1 hB
    exact h2 ((compat j2 j1 y2 y1 (hy2.trans hy1.symm)).trans h1)
  refine ⟨c j0, sep' _ (Scheme.Cover.mem_grothendieckTopology 𝒰) _ _ ?_⟩
  rintro V g ⟨W, h, g', hg', rfl⟩
  cases hg' with
  | mk j =>
    rw [res_comp', res_comp', hc j]
    congr 1
    rcases isEmpty_or_nonempty (𝒰.X j) with he | ⟨⟨y⟩⟩
    · exact sec_empty _ _
    · rw [smul_eq_of_cast _ (claim j y)]

theorem gen_bij (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤)) :
    Function.Bijective (fun k : ZMod q => k.val • twGen i ζ) := by
  refine ⟨fun k k' h => ?_, fun s => ?_⟩
  · have := cast_of_smul_eq hT ζ h
    simpa using this
  · obtain ⟨n, rfl⟩ := surj (i := i) hT ζ s
    refine ⟨(n : ZMod q), smul_eq_of_cast _ ?_⟩
    simp

theorem ResBij_of (hT : TwSec) : LateralTheory.E.HZeroPf.ResBij := by
  intro q i Y X f hY hX ⟨ζ⟩
  have : NeZero q := ⟨fun h0 => by
    subst h0
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    have h := ζ.2.1
    simp only [Nat.cast_zero, isUnit_zero_iff] at h
    exact zero_ne_one h⟩
  have h1 := gen_bij (i := i) hT ζ
  have h2 := gen_bij (i := i) hT (ζ.map f.appTop.hom)
  have e : (Sec.res (F := tw q i) f) ∘ (fun k : ZMod q => k.val • twGen i ζ) =
      fun k : ZMod q => k.val • twGen i (ζ.map f.appTop.hom) := by
    funext k
    simp only [Function.comp]
    rw [res_nsmul', (hT q i).2.2.2.1]
  exact (Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)

end LateralTheory.E.ResBijPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RootAICPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace LateralTheory.E.RootAICPf

open LateralTheory.E.t_E2Cut

theorem evalMap {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) (q : ℕ) (a : R) :
    φ ((cyclotomic q R).eval a) = (cyclotomic q K).eval (φ a) := by
  rw [← map_cyclotomic q φ, Polynomial.eval_map, Polynomial.eval₂_hom]

theorem aeval_eq {R : Type} [CommRing R] (q : ℕ) (a : R) :
    aeval a (cyclotomic q ℤ) = (cyclotomic q R).eval a := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

theorem localRoot {q : ℕ} {X : Scheme.{0}} [IsIntegral X] (hX : AICSch X) (hq : q ≠ 0)
    (hK : ((q : ℕ) : X.functionField) ≠ 0) (V : X.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ ζ : Γ(X, V), IsPrimitiveRoot (X.germToFunctionField V ζ) q := by
  have hA := hX.2 V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)
  obtain ⟨a, ha⟩ := hA (cyclotomic q Γ(X, V)) (cyclotomic.monic q _)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
  refine ⟨a, ?_⟩
  have : NeZero ((q : ℕ) : X.functionField) := ⟨hK⟩
  rw [← isRoot_cyclotomic_iff]
  show (cyclotomic q _).eval _ = 0
  rw [← evalMap, ha, map_zero]

theorem RootAIC_of : LateralTheory.E.HZeroPf.RootAIC := by
  intro q X hX hq
  haveI := hX.1
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x0, trivial⟩⟩
  have hK : ((q : ℕ) : X.functionField) ≠ 0 := by
    intro h
    have := hq.map (X.germToFunctionField ⊤).hom
    rw [map_natCast] at this
    rw [h] at this
    exact not_isUnit_zero this
  have hq0 : q ≠ 0 := by rintro rfl; exact hK (by simp)
  haveI : NeZero q := ⟨hq0⟩
  have hnb : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hx⟩
  obtain ⟨V0, hV0, hx0⟩ := hnb x0
  haveI : Nonempty V0 := ⟨⟨x0, hx0⟩⟩
  obtain ⟨ζ0, hζ0⟩ := localRoot hX hq0 hK V0 hV0
  obtain ⟨s, hs⟩ := GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally (⊤ : X.Opens)
    (X.germToFunctionField V0 ζ0) (fun x _ => by
      obtain ⟨V, hV, hx⟩ := hnb x
      haveI hne : Nonempty V := ⟨⟨x, hx⟩⟩
      obtain ⟨ζ, hζ⟩ := localRoot hX hq0 hK V hV
      obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hζ0.pow_eq_one
      exact ⟨V, hne, ζ ^ k, hx, le_top, by rw [map_pow]; exact hk⟩)
  refine ⟨⟨s, hq, ?_⟩⟩
  apply Scheme.germToFunctionField_injective X ⊤
  have : NeZero ((q : ℕ) : X.functionField) := ⟨hK⟩
  rw [aeval_eq, map_zero]
  show (X.germToFunctionField ⊤).hom _ = 0
  rw [evalMap]
  show (cyclotomic q _).eval ((X.germToFunctionField ⊤) s) = 0
  rw [hs]
  exact (isRoot_cyclotomic_iff.mpr hζ0)

end LateralTheory.E.RootAICPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SHAlgSecPf
section
noncomputable section
open CategoryTheory Limits IsLocalRing

namespace LateralTheory.E.SHAlgSecPf

theorem retract_alg {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] [Algebra.Etale A R] (Q : Ideal R) [Q.IsPrime]
    (hQ : (Q.comap (algebraMap A R)).IsMaximal) : Nonempty (R →ₐ[A] A) := by
  have hQm : Q.comap (algebraMap A R) = maximalIdeal A := IsLocalRing.eq_maximalIdeal hQ
  have hEt : Algebra.IsEtaleAt A Q := by
    have h := (Algebra.etaleLocus_eq_univ_iff_etale (R := A) (A := R)).mpr inferInstance
    have : (⟨Q, inferInstance⟩ : PrimeSpectrum R) ∈ Algebra.etaleLocus A R := by rw [h]; trivial
    exact this
  obtain ⟨g, hgQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let Rg := Localization.Away g
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid R) : Set R) (Q : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hgQ
  let Q' : Ideal Rg := Q.map (algebraMap R Rg)
  have hQ'p : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Rg Q ‹_› hdisj
  have hQ'c : Q'.comap (algebraMap R Rg) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Rg ‹_› hdisj
  have hcomap : Q'.comap (algebraMap A Rg) = RingHom.ker (algebraMap A (ResidueField A)) := by
    rw [IsScalarTower.algebraMap_eq A R Rg, ← Ideal.comap_comap, hQ'c, hQm,
      ResidueField.algebraMap_eq, ker_residue]
  obtain ⟨φ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := A) (K := ResidueField A) Q' hcomap
  obtain ⟨ψ, -⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale (R := A) (A := Rg) (B := A)
    (C := ResidueField A) (maximalIdeal A) (Algebra.ofId A (ResidueField A))
    (residue_surjective) (fun b => by
      simp [Algebra.ofId_apply, ResidueField.algebraMap_eq, residue_eq_zero_iff]) φ
  exact ⟨ψ.comp (IsScalarTower.toAlgHom A R Rg)⟩

theorem SHAlgSec_of : LateralTheory.E.SHSectionPf.SHAlgSec := by
  intro A R f hA hf hQ
  obtain ⟨hH, hS⟩ := hA
  let := f.hom.toAlgebra
  have : Algebra.Etale A R := (RingHom.etale_algebraMap).mp hf
  obtain ⟨Q, hQp, hQm⟩ := hQ
  obtain ⟨σ⟩ := retract_alg (A := A) (R := R) Q hQm
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  ext a
  exact σ.commutes a

end LateralTheory.E.SHAlgSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkGermPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.StalkGermPf

abbrev toO {X S : Scheme.{0}} (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback p (S.fromSpecStalk s) ⟶ overO p U :=
  pullback.map p (S.fromSpecStalk s) p U.ι (𝟙 _) (U.fromSpecStalkOfMem s hs) (𝟙 _) (by simp) (by simp)

def StalkCont : Prop := Cont → Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
  [QuasiCompact p] [QuasiSeparated p], IsUnit (q : Γ(S, ⊤)) → ∀ (i n : ℤ) (s : S),
  (∀ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i), pull _ (sch.map (toO p s U hs)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ z : Ht q (sch.obj (pullback p (S.fromSpecStalk s))) n i, ∃ (U : S.Opens) (hs : s ∈ U) (x : Ht q (sch.obj (overO p U)) n i),
    pull _ (sch.map (toO p s U hs)) _ _ x = z)

variable {Y X S : Scheme.{0}}

theorem pull_mc {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (x : Ht q (sch.obj C) n i) :
    pull _ (sch.map (a ≫ b)) (tw q i) n x = pull _ (sch.map a) _ _ (pull _ (sch.map b) _ _ x) := by
  rw [Functor.map_comp, pull_comp]

theorem toO_res (p : X ⟶ S) (s : S) {V U : S.Opens} (h : V ≤ U) (hV : s ∈ V) :
    toO p s V hV ≫ resO p h = toO p s U (h hV) := by
  have e : V.fromSpecStalkOfMem s hV ≫ S.homOfLE h = U.fromSpecStalkOfMem s (h hV) := by
    rw [← cancel_mono U.ι]; simp
  simp only [toO, resO]; rw [pullback.map_comp]; congr 1 <;> simp [e]

theorem toO_f (f : Y ⟶ X) (p : X ⟶ S) (s : S) (U : S.Opens) (hs : s ∈ U) :
    pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ toO p s U hs =
      toO (f ≫ p) s U hs ≫ fO f p U := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_f (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem res_res (p : X ⟶ S) {W V U : S.Opens} (h1 : W ≤ V) (h2 : V ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  simp only [toO, resO, fO]; rw [pullback.map_comp]; try rw [pullback.map_comp]
  all_goals (try congr 1) <;> simp

theorem StalkGerm_of (hS : StalkCont) : StalkGerm := by
  intro hC hH q Y X S f p _ _ _ _ _ _ hq i s he n
  obtain ⟨ia, sa⟩ := hS hC hH q p hq i n s
  obtain ⟨ib, -⟩ := hS hC hH q (f ≫ p) hq i n s
  have hb := he n
  constructor
  · intro U hs x hx
    apply ia U hs x
    apply hb.1
    rw [map_zero, ← pull_mc, toO_f, pull_mc, hx, map_zero]
  · intro U hs y
    obtain ⟨w, hw⟩ := hb.2 (pull _ (sch.map (toO (f ≫ p) s U hs)) _ _ y)
    obtain ⟨U1, hs1, x1, hx1⟩ := sa w
    have hs2 : s ∈ U ⊓ U1 := ⟨hs, hs1⟩
    have hx2' : pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n
        (pull (ZMod q) (sch.map (resO p (inf_le_right : U ⊓ U1 ≤ U1))) (tw q i) n x1) = w := by
      rw [← pull_mc, toO_res]; exact hx1
    obtain ⟨x2, hx2⟩ : ∃ x2 : H (ZMod q) (sch.obj (overO p (U ⊓ U1))) (tw q i) n,
        pull (ZMod q) (sch.map (toO p s (U ⊓ U1) hs2)) (tw q i) n x2 = w := ⟨_, hx2'⟩
    have e1 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _ (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) =
        pull _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _)
          (by simp) (by simp))) (tw q i) n (pull _ (sch.map (toO p s (U ⊓ U1) hs2)) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, toO_f]
    have e2 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (toO (f ≫ p) s U hs)) (tw q i) n y := by
      rw [← pull_mc, toO_res]
    have h0 : pull _ (sch.map (toO (f ≫ p) s (U ⊓ U1) hs2)) _ _
        (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2 -
          pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) = 0 := by
      rw [map_sub, e1, e2, hx2, hw, sub_self]
    obtain ⟨V, hV, hsV, hd⟩ := ib _ hs2 _ h0
    refine ⟨V, hV.trans inf_le_left, hsV, pull _ (sch.map (resO p hV)) _ _ x2, ?_⟩
    rw [map_sub, sub_eq_zero] at hd
    have g1 : pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p hV)) _ _ x2) =
        pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n (pull _ (sch.map (fO f p (U ⊓ U1))) _ _ x2) := by
      rw [← pull_mc, ← pull_mc, res_f]
    have g2 : pull _ (sch.map (resO (f ≫ p) hV)) (tw q i) n
        (pull _ (sch.map (resO (f ≫ p) (inf_le_left : U ⊓ U1 ≤ U))) _ _ y) =
        pull _ (sch.map (resO (f ≫ p) (hV.trans inf_le_left))) (tw q i) n y := by
      rw [← pull_mc, res_res]
    rw [g1, hd, g2]

end LateralTheory.E.StalkGermPf
end
end

