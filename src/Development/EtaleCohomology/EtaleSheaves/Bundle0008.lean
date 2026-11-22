import Development.EtaleCohomology.EtaleSheaves.Bundle0004
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlobalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.GlobalPf

def gam {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) : T ⟶ Γ(X, V) :=
  (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V (by simp)

def Affine : Prop := ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K) {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens),
  IsAffineOpen V → BC q i k (gam p V) → Eqv _ (sch.map (pullback.fst p (Spec.map k) ∣_ V)) (tw q i)

def LocEt : Prop := ∀ {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p] (x : X),
  ∃ (U : X.Opens) (n : ℕ), x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U →
    ∃ c : CommRingCat.of (MvPolynomial (Fin n) T) ⟶ Γ(X, V), Et c ∧
      CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T) ≫ c = gam p V

theorem Global_of (hZ : ZarLocal) (hA : Affine) (hL : LocEt) : Global := by
  intro H q i T K k hG X p _
  refine hZ H (ZMod q) (tw q i) (pullback.fst p (Spec.map k)) fun x => ?_
  obtain ⟨U, n, hx, hU⟩ := hL p x
  refine ⟨U, hx, fun V hV hVU => ?_⟩
  obtain ⟨c, hc, hcg⟩ := hU V hV hVU
  have hb := hG n _ c hc
  rw [hcg] at hb
  exact hA q i k p V hV hb

end LateralTheory.E.GlobalPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HZeroPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.HZeroPf

open LateralTheory.E.t_E2Cut

def RootAIC : Prop := ∀ (q : ℕ) (X : Scheme.{0}), AICSch X → IsUnit (q : Γ(X, ⊤)) → Nonempty (Prim q Γ(X, ⊤))

def ResBij : Prop := ∀ (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X), ConnectedSpace Y → ConnectedSpace X →
  Nonempty (Prim q Γ(X, ⊤)) → Function.Bijective (Sec.res (F := tw q i) f)

theorem connected_of_AICSch {X : Scheme.{0}} (h : AICSch X) : ConnectedSpace X := by
  have := h.1
  infer_instance

theorem HZero_of (hR : RootAIC) (hB : ResBij) : LateralTheory.E.t_E2Cut.HZero := by
  intro hyp q Y X f hX hY hq i
  obtain ⟨_, e, he, _⟩ := hyp.a9 (ZMod q) (tw q i)
  have := connected_of_AICSch hX
  have hres := hB q i f hY (connected_of_AICSch hX) (hR q X hX hq)
  have key : (pull (ZMod q) (sch.map f) (tw q i) 0) = (e Y).toAddMonoidHom.comp
      ((AddMonoidHom.mk' (Sec.res (F := tw q i) f) (fun a b => map_add _ a b)).comp (e X).symm.toAddMonoidHom) := by
    ext x
    obtain ⟨s, rfl⟩ := (e X).surjective x
    simp [he]
  rw [key]
  exact (e Y).bijective.comp (hres.comp (e X).symm.bijective)

end LateralTheory.E.HZeroPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HensIdemCut
section
noncomputable section
open Polynomial

namespace LateralTheory.E.HensIdemCut

def LJac : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → I.map φ ≤ Ideal.jacobson ⊥

def LMonic : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → ∀ b : B, b * b - b ∈ I.map φ → ∃ (N : ℕ) (f : A[X]), f.Monic ∧ f.eval₂ φ b = 0 ∧
    f.map (Ideal.Quotient.mk I) = X ^ N * (X - C 1) ^ N

def LFactor : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (f : A[X]) (g₀ h₀ : (A ⧸ I)[X]),
  f.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
  ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧ g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀

def LIdem : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (B : Type) [CommRing B] (φ : A →+* B),
  I.map φ ≤ Ideal.jacobson ⊥ → ∀ (b : B), b * b - b ∈ I.map φ → ∀ (N : ℕ) (g h : A[X]),
  g.map (Ideal.Quotient.mk I) = X ^ N → h.map (Ideal.Quotient.mk I) = (X - C 1) ^ N →
  g.eval₂ φ b * h.eval₂ φ b = 0 → ∃ x : B, IsIdempotentElem x ∧ x - b ∈ I.map φ

theorem goal_of (hJ : LJac) (hM : LMonic) (hF : LFactor) (hI : LIdem) : LateralTheory.E.t_E1Cut.HensIdem := by
  intro A _ I _ B _ φ hφ
  refine ⟨hJ A I B φ hφ, ?_⟩
  intro e he
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hb : b * b - b ∈ I.map φ := by
    rw [← Ideal.Quotient.eq]
    simpa [IsIdempotentElem] using he
  obtain ⟨N, f, hfm, hf0, hfI⟩ := hM A I B φ hφ b hb
  have hcop : IsCoprime ((X : (A ⧸ I)[X]) ^ N) ((X - C 1) ^ N) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - C 1) from ⟨1, -1, by rw [C_1]; ring⟩).pow
  obtain ⟨g, h, -, -, rfl, hg, hh⟩ :=
    hF A I f _ _ hfm ((monic_X).pow N) ((monic_X_sub_C 1).pow N) hcop hfI
  obtain ⟨x, hx, hxb⟩ := hI A I B φ (hJ A I B φ hφ) b hb N g h hg hh (by rw [← eval₂_mul]; exact hf0)
  exact ⟨x, hx, Ideal.Quotient.eq.mpr hxb⟩

end LateralTheory.E.HensIdemCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HensIntPf
section
noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.HensIntPf

theorem local_of_finite (A S : Type) [CommRing A] [HenselianLocalRing A] [CommRing S] [Algebra A S]
    [Module.Finite A S] [Nontrivial S] (hid : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨q, hq, fun n hn => ?_⟩
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian A q
  rcases hid e he with h | h
  · exact absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)
  · exact (H n hn).1 (h ▸ fun h1 => hn.ne_top ((Ideal.eq_top_iff_one n).2 h1))

theorem sub_finite (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (Algebra.adjoin A (s : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)

theorem sub_local (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) : IsLocalRing (Algebra.adjoin A (s : Set B)) := by
  haveI := sub_finite A B s
  refine local_of_finite A _ fun e he => ?_
  rcases hid e (by have h := congrArg Subtype.val he.eq; exact h) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem isLocal (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  haveI := sub_local A B hid {x}
  let y : Algebra.adjoin A ((({x} : Finset B)) : Set B) := ⟨x, Algebra.subset_adjoin (by simp)⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with h | h
  · exact Or.inl (h.map (Algebra.adjoin A _).val)
  · exact Or.inr (by simpa [y] using h.map (Algebra.adjoin A _).val)

theorem maxIdeal_comap (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) :
    letI := isLocal A B hid
    letI := sub_local A B hid s
    (maximalIdeal B).comap (Algebra.adjoin A (s : Set B)).val = maximalIdeal (Algebra.adjoin A (s : Set B)) := by
  letI := isLocal A B hid
  letI := sub_local A B hid s
  haveI : Algebra.IsIntegral (Algebra.adjoin A (s : Set B)) B := Algebra.IsIntegral.tower_top A
  have : ((maximalIdeal B).comap (algebraMap (Algebra.adjoin A (s : Set B)) B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  exact IsLocalRing.eq_maximalIdeal this

theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : HenselianLocalRing B := by
  classical
  letI := isLocal A B hid
  refine ⟨fun f hf a0 h0 h1 => ?_⟩
  set s : Finset B := insert a0 f.coeffs
  let S := Algebra.adjoin A (s : Set B)
  letI := sub_local A B hid s
  haveI := sub_finite A B s
  haveI : HenselianLocalRing S := GlobalTheory.henselianLocalRing_of_finite A S
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc =>
    Algebra.subset_adjoin (by simp [s, hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, Algebra.subset_adjoin (by simp [s])⟩
  have hmem : ∀ y : S, y ∈ maximalIdeal S ↔ (y : B) ∈ maximalIdeal B := fun y => by
    rw [← maxIdeal_comap A B hid s]; rfl
  have he' : ∀ (p : S[X]) (y : S), ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := fun p y => by
    rw [eval_map, ← show S.val.toRingHom y = (y : B) from rfl, eval₂_at_apply]; rfl
  have he : ∀ p : S[X], ((p.eval b0 : S) : B) = (p.map S.val.toRingHom).eval a0 := fun p => he' p b0
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian g hgm b0
    ((hmem _).2 (by rw [he, hgf]; exact h0))
    (by
      rw [← IsLocalRing.notMem_maximalIdeal, hmem, he, ← derivative_map, hgf]
      exact IsLocalRing.notMem_maximalIdeal.2 h1)
  refine ⟨a, ?_, (hmem _).1 ha'⟩
  rw [IsRoot.def, ← hgf, ← he', ha.eq_zero]; rfl

theorem HensInt_of : LateralTheory.E.t_E3Cut.HensInt := by
  intro A B _ _ _ _ f hf hid
  letI : Algebra A B := f.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hf⟩
  exact ⟨hens A B hid⟩

end LateralTheory.E.HensIntPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IECompPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.IECompPf
open LateralTheory.E.t_E3Cut

def UnderFA : Prop := ∀ X : CommRingCat.{0}, IsFinitelyAccessibleCategory.{0} (Under X)

def EtSpreads : Prop := MorphismProperty.PreIndSpreads.{0} Et

theorem et_comp : Et.IsStableUnderComposition where
  comp_mem f g hf hg := by
    show (f ≫ g).hom.Etale
    rw [CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _ hf hg

theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

theorem et_fp : Et ≤ MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := fun _ _ f hf =>
  CommRingCat.isFinitelyPresentable_hom f (RingHom.Etale.iff_flat_and_formallyUnramified.1 hf).2.2

theorem IEComp_of (h1 : UnderFA) (h2 : EtSpreads) : IEComp := by
  intro A B C f g hf hg
  have : ∀ X : CommRingCat.{0}, IsFinitelyAccessibleCategory.{0} (Under X) := h1
  have : MorphismProperty.PreIndSpreads.{0} Et := h2
  have := et_comp
  have := et_cobase
  have := MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads (P := Et) et_fp
  exact this.comp_mem f g hf hg

end LateralTheory.E.IECompPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntClosPf
section
noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IntClosPf

theorem intMul {A C : Type} [CommRing A] [CommRing C] [IsDomain C] [Algebra A C] (z : C) (p : Polynomial A)
    (hp : ∃ n, algebraMap A C (p.coeff n) ≠ 0) (hz : Polynomial.aeval z p = 0) :
    ∃ a : A, algebraMap A C a ≠ 0 ∧ IsIntegral A (algebraMap A C a * z) := by
  let A' := (algebraMap A C).range
  letI : Algebra A A' := (algebraMap A C).rangeRestrict.toAlgebra
  have : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hsurj : Function.Surjective (algebraMap A A') := (algebraMap A C).rangeRestrict_surjective
  have : Algebra.IsIntegral A A' := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hsurj x
    exact isIntegral_algebraMap⟩
  set p' := p.map (algebraMap A A') with hp'def
  have h1 : Polynomial.aeval z p' = 0 := by rw [Polynomial.aeval_map_algebraMap]; exact hz
  have hp' : p' ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := hp
    apply hn
    have : p'.coeff n = 0 := by rw [h0]; rfl
    rw [hp'def, Polynomial.coeff_map] at this
    have := congrArg Subtype.val this
    exact this
  have hint := isIntegral_leadingCoeff_smul p' z h1
  obtain ⟨a, ha⟩ := hsurj p'.leadingCoeff
  have hlc : p'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
  have hval : algebraMap A C a = (p'.leadingCoeff : C) := by rw [← ha]; rfl
  refine ⟨a, ?_, ?_⟩
  · rw [hval]; intro h; exact hlc (Subtype.ext h)
  · have h2 : algebraMap A C a * z = p'.leadingCoeff • z := by rw [Algebra.smul_def, hval]; rfl
    rw [h2]
    exact isIntegral_trans _ hint

theorem IntClos_of (hH : HensInt) : IntClos := by
  intro A C c _ hSH hAIC hAR
  obtain ⟨hHA, -⟩ := hSH
  letI : Algebra A C := c.hom.toAlgebra
  let B := integralClosure A C
  refine ⟨CommRingCat.of B, CommRingCat.ofHom (algebraMap A B), CommRingCat.ofHom B.val.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; rfl
  · intro x; exact integralClosure.isIntegral x
  · exact Subtype.val_injective
  · have hne : Nontrivial B := inferInstance
    obtain ⟨h⟩ := hH A B (algebraMap A B) (fun x => integralClosure.isIntegral x) (fun e he => by
      rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (e : C) from congrArg Subtype.val he)) with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h)
    exact h.toIsLocalRing
  · intro p hm hdeg
    have hm' : (p.map B.val.toRingHom).Monic := hm.map _
    have hdeg' : 0 < (p.map B.val.toRingHom).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective]; exact hdeg
    obtain ⟨r, hr⟩ := hAIC _ hm' hdeg'
    have hrB : IsIntegral B r := ⟨p, hm, by rw [← Polynomial.eval_map]; exact hr⟩
    have hrA : IsIntegral A r := isIntegral_trans _ hrB
    have hrM : r ∈ B := hrA
    refine ⟨⟨r, hrM⟩, Subtype.val_injective ?_⟩
    show B.val.toRingHom (p.eval ⟨r, hrM⟩) = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hr
  · intro z
    have hQ : (⊥ : Ideal C).IsPrime := Ideal.isPrime_bot
    obtain ⟨p, ⟨n, hn⟩, hz⟩ := hAR ⊥ hQ z
    obtain ⟨a, ha, hint⟩ := intMul z p ⟨n, fun h => hn (by rw [Ideal.mem_bot]; exact h)⟩
      (by rw [Ideal.mem_bot] at hz; exact hz)
    refine ⟨algebraMap A B a, ⟨_, hint⟩, fun h => ha (congrArg Subtype.val h), rfl⟩

end LateralTheory.E.IntClosPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntPBPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntPBPf

def IntHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] (φ : A →+* B), φ.IsIntegral →
  HenselianRing B ((IsLocalRing.maximalIdeal A).map φ)

def IntFib : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)), IsIntegralHom p →
  ∃ (B : Type) (_ : CommRing B) (φ : A →+* B), φ.IsIntegral ∧ ∀ (q : ℕ) (i : ℤ),
    Eqv _ (spMap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ))) (tw q i) →
    Eqv _ (sch.map (pullback.fst p (LateralTheory.E.t_E2Cut.cpt A))) (tw q i)

theorem IntPB_of (hH : IntHens) (hF : IntFib) : LateralTheory.E.t_E2Cut.IntPB := by
  intro hyp q i A _ _ hSH hq X p hp
  obtain ⟨hA, -⟩ := hSH
  obtain ⟨B, _, φ, hφ, hE⟩ := hF A p hp
  have : HenselianRing B ((IsLocalRing.maximalIdeal A).map φ) := hH A B φ hφ
  have hqB : IsUnit ((q : ℕ) : B) := by simpa using hq.map φ
  exact hE q i (hyp.e1 q B _ hqB i)

end LateralTheory.E.IntPBPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IsChernClassCocycle
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.AlexanderWhitneyCupPullbackNaturality

def pcoc {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E') I n) :
    Cocycle ((chains R).obj E) I n :=
  zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)

theorem cpull_mk {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (I : Cx R) {n : ℤ} (α : Cocycle ((chains R).obj E') I n) :
    cpull ((chains R).map f) I n (CohomologyClass.mk α) = CohomologyClass.mk (pcoc f α) := rfl

theorem pull_mk {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) {n : ℤ}
    (α : Cocycle ((chains R).obj E') (res R F) n) : pull R f F n (CohomologyClass.mk α) = CohomologyClass.mk (pcoc f α) := rfl

theorem sub_map {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (Sx.map f x).sub j l h = Sx.map f (x.sub j l h) := by
  simp only [Sx.sub, Sx.map]
  rw [← FunctorToTypes.comp, ← FunctorToTypes.comp, NatTrans.naturality]

theorem inv_pull {q : ℕ} {E E' : Spc} (f : E ⟶ E') (h : Inv q E') : Inv q E :=
  fun U ⟨x⟩ => h U ⟨Sx.map f x⟩

def LeafEvPull : Prop := ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ}
  (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U),
  ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (Sx.map f x)

def LeafCupAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
  ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1

def LeafCupSpec : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
  ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k,
    ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def OneProp (q : ℕ) (E : Spc) (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ

def LeafOneEx : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α, OneProp q E α

def LeafOneUniq : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ α β, OneProp q E α → OneProp q E β →
  CohomologyClass.mk α = CohomologyClass.mk β

def IsChernClassCocycle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
  (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
    ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
  ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
    w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
    ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def ChernClassExists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ, IsChernClassCocycle q L γ

def ChernClassUnique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ γ δ, IsChernClassCocycle q L γ → IsChernClassCocycle q L δ →
  CohomologyClass.mk γ = CohomologyClass.mk δ

def KumProp (q : ℕ) {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) : Prop :=
  (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
  ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
    ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def LeafKumEx : Prop := ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∃ γ, KumProp q u γ

def LeafKumUniq : Prop := ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∀ γ δ,
  KumProp q u γ → KumProp q u δ → CohomologyClass.mk γ = CohomologyClass.mk δ

theorem units_map_comp {Y X U : Scheme.{0}} (x : U ⟶ Y) (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map (x ≫ f).appTop.hom.toMonoidHom u = Units.map x.appTop.hom.toMonoidHom (Units.map f.appTop.hom.toMonoidHom u) := by
  ext
  change (x ≫ f).appTop.hom (u : Γ(X, ⊤)) = x.appTop.hom (f.appTop.hom u)
  simp
  rfl

section Glue
variable (hE : LeafEvPull)
include hE

theorem ev_pcoc {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E') I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (pcoc f α).1 p s h U x = ev α.1 p s h U (Sx.map f x) := hE R f α.1 p s h U x

theorem isAW_pull {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) {α : Cocycle ((chains R).obj E') I n} {β : Cocycle ((chains R).obj E') J m}
    {γ : Cocycle ((chains R).obj E') K k} (h : μ.IsAW hk α.1 β.1 γ.1) :
    μ.IsAW hk (pcoc f α).1 (pcoc f β).1 (pcoc f γ).1 := by
  intro N w hw U x
  refine (hE R f γ.1 N w hw U x).trans ((h N w hw U (Sx.map f x)).trans (Finset.sum_congr rfl fun p _ => ?_))
  rw [sub_map, sub_map, ev_pcoc hE, ev_pcoc hE]

theorem cup_nat (hA : LeafCupAW) (hS : LeafCupSpec) {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc}
    (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k) (a : CohomologyClass ((chains R).obj E') I n)
    (b : CohomologyClass ((chains R).obj E') J m) :
    cpull ((chains R).map f) K k (μ.cup E' hk a b) =
      μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := hA R μ E' hk α β
  have e1 : μ.cup E' hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    pick_spec (hS R μ E' hk) α β γ hγ
  have e2 : μ.cup E hk (CohomologyClass.mk (pcoc f α)) (CohomologyClass.mk (pcoc f β)) = CohomologyClass.mk (pcoc f γ) :=
    pick_spec (hS R μ E hk) _ _ _ (isAW_pull hE μ f hk hγ)
  rw [e1, cpull_mk, cpull_mk, cpull_mk, e2]

theorem one_eq (hX : LeafOneEx) (hU : LeafOneUniq) {q : ℕ} [NeZero q] {E : Spc} (h : Inv q E)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : OneProp q E α) : one q E = CohomologyClass.mk α := by
  obtain ⟨α0, hα0⟩ := hX q E h
  obtain ⟨β, hβ, hβp⟩ : ∃ β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk β = one q E ∧ OneProp q E β :=
    pick_spec (P := fun c => ∃ β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk β = c ∧ OneProp q E β)
      ⟨_, α0, rfl, hα0⟩
  rw [← hβ]
  exact hU q E h β α hβp hα

theorem c1_eq (hX : ChernClassExists) (hU : ChernClassUnique) {q : ℕ} [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : Inv q E)
    (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hγ : IsChernClassCocycle q L γ) : c1 q L = CohomologyClass.mk γ := by
  obtain ⟨α0, hα0⟩ := hX q L h
  obtain ⟨β, hβ, hβp⟩ : ∃ β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk β = c1 q L ∧ IsChernClassCocycle q L β :=
    pick_spec (P := fun c => ∃ β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk β = c ∧ IsChernClassCocycle q L β)
      ⟨_, α0, rfl, hα0⟩
  rw [← hβ]
  exact hU q L h β γ hβp hγ

theorem kum_eq (hX : LeafKumEx) (hU : LeafKumUniq) {q : ℕ} [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (h : IsUnit (q : Γ(X, ⊤)))
    (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (hγ : KumProp q u γ) : kum q u = CohomologyClass.mk γ := by
  obtain ⟨α0, hα0⟩ := hX q u h
  obtain ⟨β, hβ, hβp⟩ : ∃ β : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      CohomologyClass.mk β = kum q u ∧ KumProp q u β :=
    pick_spec (P := fun c => ∃ β : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      CohomologyClass.mk β = c ∧ KumProp q u β) ⟨_, α0, rfl, hα0⟩
  rw [← hβ]
  exact hU q u h β γ hβp hγ

end Glue

theorem goal_of (h1 : LeafEvPull) (h2 : LeafCupAW) (h3 : LeafCupSpec) (h4 : LeafOneEx) (h5 : LeafOneUniq) (h6 : ChernClassExists)
    (h7 : ChernClassUnique) (h8 : LeafKumEx) (h9 : LeafKumUniq) : LateralTheory.E.D2.LeafA6nat := by
  intro q _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f n m i j a b
    exact cup_nat h1 h2 h3 (twPair q i j) f rfl a b
  · intro E E' f h'
    obtain ⟨α, hα⟩ := h4 q E' h'
    rw [one_eq h1 h4 h5 h' α hα, pull_mk, one_eq h1 h4 h5 (inv_pull f h') (pcoc f α)]
    intro U x ζ
    exact (ev_pcoc h1 f α 0 0 _ U x).trans (hα U _ ζ)
  · intro E E' f L h'
    obtain ⟨γ, hγ⟩ := h6 q L h'
    rw [c1_eq h1 h6 h7 L h' γ hγ, pull_mk, c1_eq h1 h6 h7 (f ≫ L) (inv_pull f h') (pcoc f γ)]
    refine ⟨fun U x => ?_, fun U x v hv => ?_, fun U x v w hv hw => ?_⟩
    · exact (ev_pcoc h1 f γ 0 2 _ U x).trans (hγ.1 U _)
    · exact (ev_pcoc h1 f γ 1 1 _ U x).trans (hγ.2.1 U _ v hv)
    · refine (ev_pcoc h1 f γ 2 0 _ U x).trans (hγ.2.2 U _ v w ?_ ?_)
      · rw [sub_map]; exact hv
      · rw [sub_map]; exact hw
  · intro Y X f u hq
    have hq' : IsUnit (q : Γ(Y, ⊤)) := by simpa using hq.map f.appTop.hom
    obtain ⟨γ, hγ⟩ := h8 q u hq
    rw [kum_eq h1 h8 h9 u hq γ hγ, pull_mk, kum_eq h1 h8 h9 _ hq' (pcoc (sch.map f) γ)]
    refine ⟨fun U x => ?_, fun U x v hv => ?_⟩
    · exact (ev_pcoc h1 (sch.map f) γ 1 0 _ U x).trans (hγ.1 U (x ≫ f))
    · exact (ev_pcoc h1 (sch.map f) γ 0 1 _ U x).trans (hγ.2 U (x ≫ f) v (hv.trans (units_map_comp x f u).symm))

end LateralTheory.E.AlexanderWhitneyCupPullbackNaturality
end
end

