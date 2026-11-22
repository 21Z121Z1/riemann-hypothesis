import Development.EtaleCohomology.EtaleSheaves.Bundle0007
import Development.EtaleCohomology.EtaleSheaves.Bundle0015
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Development.EtaleCohomology.EtaleSheaves.Bundle0014
import Development.EtaleCohomology.EtaleSheaves.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.LeafExcRingPf

-- bundled from Development.EtaleCohomology.EtaleSheaves.CxDescPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CxDescPf

abbrev tr {R : Type} [CommRing R] (K : Cx R) (N : ℕ) : Cx R :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

abbrev trm {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (N : ℕ) : tr K N ⟶ tr L N :=
  HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

def Good {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (I : Cx R) (m : ℤ) : Prop :=
  (∀ j : ℤ, j < m → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I m)

def stupid : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ((∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
    ∀ j : ℤ, Function.Bijective (cpull (trm g 0) I j)) ∧
  ∀ (m : ℤ) (N : ℕ), m + 1 ≤ (N : ℤ) → Good (trm g N) I m → Good g I m

def long : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ) (N : ℕ),
  Good ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) I m →
  Good (trm g N) I m → Good (trm g (N + 1)) I m

def shift : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (p : ℕ) (j : ℤ),
  (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j)) ∧
  (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j))

theorem CxDesc_of (hS : stupid) (hL : long) (hH : shift) : LateralTheory.E.DescStepPf.CxDesc := by
  intro R _ I _ hI K L _ _ g n hlow hn h0
  obtain ⟨hb, hlim⟩ := hS R I hI g
  have base : Good (trm g 0) I (n + 1) := ⟨fun j _ => hb h0 j, (hb h0 (n + 1)).1⟩
  have step : ∀ N : ℕ, Good (trm g N) I (n + 1) := by
    intro N
    induction N with
    | zero => exact base
    | succ N ih =>
      refine hL R I hI g (n + 1) N ⟨fun j hj => ?_, ?_⟩ ih
      · exact (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) j).1 (hlow (N + 1) (j - ((N + 1 : ℕ) : ℤ)) (by omega))
      · apply (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) (n + 1)).2
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h
          have e : n + 1 - ((0 + 1 : ℕ) : ℤ) = n := by omega
          rw [e]; exact hn (0 + 1)
        · exact (hlow (N + 1) _ (by omega)).1
  have hg := hlim (n + 1) (n + 2).toNat (by omega) (step _)
  exact ⟨hg.1, hg.2⟩

end LateralTheory.E.CxDescPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DescIntPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescIntPf

def RelZS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {U E : Spc} (u : U ⟶ E) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R u F m)) ∧ Function.Injective (pull R u F n)

theorem relZ_iff (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    RelZ q i n f ↔ RelZS (ZMod q) (tw q i) n (sch.map (Spec.map f)) := Iff.rfl

theorem transfer (R : Type) [CommRing R] (F : Shv R) {U E X' X : Spc} (u : U ⟶ E) (f : X' ⟶ X) (a' : U ⟶ X')
    (a : E ⟶ X) (hsq : u ≫ a = a' ≫ f) (ha : Eqv R a F) (ha' : Eqv R a' F) (n : ℤ) (hu : RelZS R F n u) :
    RelZS R F n f := by
  have key : ∀ m (x : H R X F m), pull R a' F m (pull R f F m x) = pull R u F m (pull R a F m x) := by
    intro m x
    rw [← pull_comp, ← pull_comp, hsq]
  refine ⟨fun m hm y => ?_, fun x x' hxx => ?_⟩
  · obtain ⟨z, hz⟩ := hu.1 m hm (pull R a' F m y)
    obtain ⟨x, rfl⟩ := (ha m).2 z
    refine ⟨x, (ha' m).1 ?_⟩
    rw [key, hz]
  · have h1 := congrArg (pull R a' F n) hxx
    rw [key, key] at h1
    exact (ha n).1 (hu.2 h1)

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := fun n => by
  have h1 : ∀ x, pull R e.inv F n (pull R e.hom F n x) = x := fun x => by
    rw [← pull_comp, e.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R e.hom F n (pull R e.inv F n x) = x := fun x => by
    rw [← pull_comp, e.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem RelZS.of_iso (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (u : U ⟶ E) (u' : U' ⟶ E') (e₁ : U ≅ U')
    (e₂ : E ≅ E') (hsq : u ≫ e₂.hom = e₁.hom ≫ u') (n : ℤ) (hu : RelZS R F n u) : RelZS R F n u' :=
  transfer R F u u' e₁.hom e₂.hom hsq (eqv_of_iso R F e₂) (eqv_of_iso R F e₁) n hu

def EtaleRelativeIsoTruncationFromLevels : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ (p : ℕ) (m : ℤ), m < n → RelZS R F m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) →
  RelZS R F n (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) → RelZS R F n u

def CechSq : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
  ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (Spec Y')) (a : E ⟶ sch.obj (Spec C)),
    u ≫ a = a' ≫ sch.map (Spec.map φ') ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧
    (∀ p : ℕ, ∃ (L : CommRingCat.{0}) (l : A ⟶ L) (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : L ⟶ Z),
      P L l ∧ IsPushout φ l wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧
    ∃ (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : D ⟶ Z), IsPushout φ (c ≫ g) wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0))))

theorem DescInt_of (hT : EtaleRelativeIsoTruncationFromLevels) (hC : CechSq) : LateralTheory.E.StalkCut.DescInt := by
  intro hH q _ i n A Y φ hq P hpush hbelow C D c g hCc hDc hgi hgs hDn Y' w φ' hpo
  obtain ⟨U, E, u, a', a, hsq, ha, ha', hlev, Z, wz, ψ, hpo0, h0⟩ :=
    hC hH q i φ hq P @hpush c g hCc hDc hgi hgs Y' w φ' hpo
  rw [relZ_iff]
  refine transfer _ _ u _ a' a hsq ha ha' n (hT _ _ u n (fun p m hm => ?_) (h0 n (hDn Z wz ψ hpo0)))
  obtain ⟨L, l, Z', wz', ψ', hL, hpo', hrel⟩ := hlev p
  exact hrel m (hbelow m hm L l hL Z' wz' ψ' hpo')

end LateralTheory.E.DescIntPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DomOpenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.DomOpenPf

theorem algClosed_of_AIC (T : Type) [CommRing T] [IsDomain T] (hT : AIC T) :
    IsAlgClosed (FractionRing T) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  set K := FractionRing T
  set f := algebraMap T K
  have hf : Function.Injective f := IsFractionRing.injective T K
  obtain ⟨b, hb₁, hb₂⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  have hb0 : (b : T) ≠ 0 := nonZeroDivisors.ne_zero hb₁
  have hdeg : q.natDegree = p.natDegree := by
    rw [← natDegree_map_eq_of_injective hf q, hb₂, ← IsScalarTower.algebraMap_smul K b p,
      natDegree_smul_of_smul_regular]
    exact IsSMulRegular.of_ne_zero (by simpa [f] using (map_ne_zero_iff f hf).mpr hb0)
  have hpos : 0 < p.natDegree := Irreducible.natDegree_pos hirr
  have hq0 : q ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg; omega
  obtain ⟨a, ha⟩ := hT (integralNormalization q) (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  have hlc : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hf).mpr (leadingCoeff_ne_zero.mpr hq0)
  refine ⟨f a / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (p := q) (by omega) f (f a / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hlc, eval₂_at_apply, ha, map_zero] at key
  have h2 : q.eval₂ f (f a / f q.leadingCoeff) = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hlc
    · exact h
  rw [eval₂_eq_eval_map, hb₂, ← IsScalarTower.algebraMap_smul K b p, eval_smul, smul_eq_mul] at h2
  exact (mul_eq_zero.mp h2).resolve_left ((map_ne_zero_iff f hf).mpr hb0)

theorem algebraMap_ne_zero_of_flat (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [Nontrivial D]
    [Algebra T D] [Module.Flat T D] {s : T} (hs : s ≠ 0) : algebraMap T D s ≠ 0 := by
  intro h
  have hr : IsSMulRegular D s := Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  apply one_ne_zero (α := D)
  apply hr
  simp [Algebra.smul_def, h]

theorem exists_frac (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) (a : D) :
    ∃ s t : T, s ≠ 0 ∧ algebraMap T D s * a = algebraMap T D t := by
  classical
  haveI := algClosed_of_AIC T hT
  let M := nonZeroDivisors T
  let S := Localization (Algebra.algebraMapSubmonoid D M)
  have hle : Algebra.algebraMapSubmonoid D M ≤ nonZeroDivisors D := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (algebraMap_ne_zero_of_flat T D (nonZeroDivisors.ne_zero hs))
  have : IsDomain S := IsLocalization.isDomain_localization hle
  have : IsLocalization (M.map (algebraMap T D)) S := inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid D M) S)
  have : Algebra.FormallyEtale (FractionRing T) S :=
    Algebra.FormallyEtale.localization_map M (Rₘ := FractionRing T) (Sₘ := S) (S := D)
  have : Algebra.EssFiniteType (FractionRing T) S := Algebra.EssFiniteType.of_comp T (FractionRing T) S
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) S
  have hsub : Subsingleton (PrimeSpectrum S) := by
    constructor
    intro p q
    by_contra hpq
    have h0 : ((fun r => if r = p then (1 : FractionRing T) else 0) * fun r => if r = q then 1 else 0) = 0 := by
      funext r; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs with h1 h2 <;> simp_all
    have : e.symm (fun r => if r = p then (1 : FractionRing T) else 0) * e.symm (fun r => if r = q then 1 else 0) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp this with h | h
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) p
      simp at this
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) q
      simp at this
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum S) := inferInstance
  set x := algebraMap D S a
  have hx : algebraMap (FractionRing T) S (e x p₀) = x := by
    apply e.injective
    funext p
    rw [AlgEquiv.commutes]
    simp [Subsingleton.elim p p₀]
  generalize e x p₀ = c at hx
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective M c
  change IsLocalization.mk' (FractionRing T) t s = c at hts
  refine ⟨s, t, nonZeroDivisors.ne_zero s.2, ?_⟩
  apply IsLocalization.injective S hle
  rw [map_mul, ← IsScalarTower.algebraMap_apply T D S, ← IsScalarTower.algebraMap_apply T D S,
    show algebraMap D S a = x from rfl, ← hx, ← hts,
    IsScalarTower.algebraMap_apply T (FractionRing T) S (s : T), IsScalarTower.algebraMap_apply T (FractionRing T) S t,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

theorem isEpi (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) : Algebra.IsEpi T D := by
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro a
  obtain ⟨s, t, hs, hst⟩ := exists_frac T D hT a
  have hr : IsSMulRegular (TensorProduct T D D) s :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  rw [← sub_eq_zero]
  apply hr
  change s • (1 ⊗ₜ[T] a - a ⊗ₜ[T] 1) = s • (0 : TensorProduct T D D)
  have hsa : s • a = t • (1 : D) := by rw [Algebra.smul_def, hst, Algebra.smul_def, mul_one]
  have e1 : s • ((1 : D) ⊗ₜ[T] a) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [← TensorProduct.tmul_smul, hsa, TensorProduct.tmul_smul]
  have e2 : s • (a ⊗ₜ[T] (1 : D)) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [TensorProduct.smul_tmul', hsa, ← TensorProduct.smul_tmul']
  rw [smul_zero, smul_sub, e1, e2, sub_self]

theorem DomOpen_of : LateralTheory.E.EtAICPf.DomOpen := by
  intro T D _ _ _ _ _ _ hT
  set f := CommRingCat.ofHom (algebraMap T D)
  have : Algebra.IsEpi T D := isEpi T D hT
  have : Epi f := CommRingCat.epi_iff_epi.mpr inferInstance
  have : Mono (Spec.map f) := inferInstanceAs (Mono (Scheme.Spec.map f.op))
  have : Flat (Spec.map f) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map f) :=
    (LocallyOfFinitePresentation.SpecMap_iff f).mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact IsOpenImmersion.of_flat_of_mono _

end LateralTheory.E.DomOpenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtAffNbhdPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.EtAffNbhdPf

theorem EtAffNbhd_of : LateralTheory.E.SHSectionPf.EtAffNbhd := by
  intro A _ V g hg _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let x : Spec A := ⟨m, hm.isPrime⟩
  obtain ⟨v, hv⟩ := g.surjective x
  let 𝒰 := V.affineCover
  obtain ⟨p, hp⟩ := 𝒰.covers v
  let ι := 𝒰.f (𝒰.idx v)
  have : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (𝒰.f (𝒰.idx v)))
  have : Etale ι := inferInstance
  have : Etale (ι ≫ g) := inferInstance
  let f : A ⟶ _ := Spec.preimage (ι ≫ g)
  have hfg : Spec.map f = ι ≫ g := Spec.map_preimage _
  refine ⟨_, f, ι, ?_, hfg.symm, p.asIdeal, p.isPrime, ?_⟩
  · have : Etale (Spec.map f) := by have h := ‹Etale (ι ≫ g)›; rw [← hfg] at h; exact h
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  · have h1 : (Spec.map f).base p = x := by
      rw [hfg]
      change g.base (ι.base p) = x
      rw [hp, hv]
    have h2 : ((Spec.map f).base p).asIdeal = p.asIdeal.comap f.hom := rfl
    rw [← h2, h1]
    exact hm

end LateralTheory.E.EtAffNbhdPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtAlgPf
section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.EtAlgPf

theorem key (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (c : B) : ∃ p : Polynomial A, (∃ n, algebraMap A B (p.coeff n) ∉ Q) ∧ p.eval₂ (algebraMap A B) c ∈ Q := by
  let P := Q.comap (algebraMap A B)
  have : Q.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  have : Algebra.IsUnramifiedAt A Q := inferInstance
  have : Module.Finite P.ResidueField Q.ResidueField := inferInstance
  have : IsScalarTower A P.ResidueField Q.ResidueField := inferInstance
  set x := algebraMap B Q.ResidueField c
  have hx : IsIntegral P.ResidueField x := Algebra.IsIntegral.isIntegral x
  let p := minpoly P.ResidueField x
  have hp0 : p ≠ 0 := minpoly.ne_zero hx
  let M := nonZeroDivisors (A ⧸ P)
  let q := IsLocalization.integerNormalization M p
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec M p
  have hq0 : q ≠ 0 := by
    intro h; exact hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h)
  have hqm : q.map (algebraMap (A ⧸ P) P.ResidueField) = Polynomial.C (algebraMap (A ⧸ P) P.ResidueField b) * p := by
    rw [hb.2, ← Polynomial.smul_eq_C_mul, algebraMap_smul]
  obtain ⟨r, hr⟩ := Polynomial.map_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q
  obtain ⟨n, hn⟩ : ∃ n, q.coeff n ≠ 0 := by
    by_contra h; push_neg at h; exact hq0 (Polynomial.ext h)
  refine ⟨r, ⟨n, ?_⟩, ?_⟩
  · intro hm; apply hn
    rw [← hr, Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact hm
  · rw [← Ideal.algebraMap_residueField_eq_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]
    have e1 : algebraMap A Q.ResidueField = (algebraMap P.ResidueField Q.ResidueField).comp
        ((algebraMap (A ⧸ P) P.ResidueField).comp (Ideal.Quotient.mk P)) := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (A ⧸ P) P.ResidueField,
        ← IsScalarTower.algebraMap_apply A P.ResidueField Q.ResidueField]
    rw [e1, ← Polynomial.eval₂_map, ← Polynomial.map_map, hr, hqm, ← Polynomial.aeval_def, map_mul,
      minpoly.aeval, mul_zero]

theorem EtAlg_of : LateralTheory.E.AlgResPropsPf.EtAlg := by
  intro A B f hf
  let _ := f.hom.toAlgebra
  have : Algebra.Etale A B := hf
  intro Q hQ c
  exact key A B Q c

end LateralTheory.E.EtAlgPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtLocOfOpens
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafCov2Pf
open LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcRingPf

theorem etLoc_of_opens (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop)
    (hP : ∀ {V V' : Scheme.{0}} (j : V' ⟶ V) (k : V ⟶ T), P V k → P V' (j ≫ k))
    {s : Type} (O : s → T.Opens) (hO : TopologicalSpace.IsOpenCover O) (hι : ∀ i, P _ (O i).ι) :
    EtLoc T P := by
  refine ⟨Sieve.ofArrows _ (T.openCoverOfIsOpenCover O hO).f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology _), ?_⟩
  rintro V k ⟨W', j, g, hg, rfl⟩
  cases hg with
  | mk i => exact hP _ _ (hι i)

theorem agree_at {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B) (hQ : QIso α I)
    (U : (Spec (CommRingCat.of B)).Opens) (hU : IsCompl' I U) (T : Scheme.{0})
    (a b : T ⟶ Spec (CommRingCat.of W))
    (h : a ≫ Spec.map (CommRingCat.ofHom α) = b ≫ Spec.map (CommRingCat.ofHom α)) (t : T)
    (ht : (a ≫ Spec.map (CommRingCat.ofHom α)) t ∉ U) :
    T.fromSpecResidueField t ≫ a = T.fromSpecResidueField t ≫ b := by
  set c := T.fromSpecResidueField t
  set φa := Spec.preimage (c ≫ a)
  set φb := Spec.preimage (c ≫ b)
  have ea : Spec.map φa = c ≫ a := Spec.map_preimage _
  have eb : Spec.map φb = c ≫ b := Spec.map_preimage _
  have hab : CommRingCat.ofHom α ≫ φa = CommRingCat.ofHom α ≫ φb := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc, h]
  have hI : I ≤ (show PrimeSpectrum B from (a ≫ Spec.map (CommRingCat.ofHom α)) t).asIdeal := by
    by_contra hn
    exact ht ((hU _).2 hn)
  obtain ⟨s⟩ : Nonempty (Spec (T.residueField t)) := ⟨IsLocalRing.closedPoint (T.residueField t)⟩
  have hpt : (a ≫ Spec.map (CommRingCat.ofHom α)) t = Spec.map (CommRingCat.ofHom α ≫ φa) s := by
    rw [Spec.map_comp, ea, Category.assoc, Scheme.Hom.comp_apply c, Scheme.fromSpecResidueField_apply]
  have hkill : ∀ x ∈ I, φa (α x) = 0 := by
    intro x hx
    have hx' := hI hx
    rw [hpt] at hx'
    change x ∈ Ideal.comap (CommRingCat.ofHom α ≫ φa).hom (show PrimeSpectrum (T.residueField t) from s).asIdeal at hx'
    have hb : (show PrimeSpectrum (T.residueField t) from s).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [Ideal.mem_comap, hb] at hx'
    simpa using hx'
  have hab' : ∀ x, φa (α x) = φb (α x) := fun x => by
    have := congrArg (fun f => f.hom x) hab
    simpa using this
  have hφ : φa = φb := by
    ext w
    obtain ⟨q, hq⟩ := hQ.2 (Ideal.Quotient.mk (I.map α) w)
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hq
    have hk : ∀ φ : CommRingCat.of W ⟶ T.residueField t, (∀ x ∈ I, φ (α x) = 0) →
        ∀ y ∈ I.map α, φ y = 0 := by
      intro φ hφ y hy
      have : I.map α ≤ RingHom.ker φ.hom :=
        Ideal.map_le_iff_le_comap.2 fun x hx => by simpa [RingHom.mem_ker] using hφ x hx
      exact this hy
    have h1 := hk φa hkill _ hq
    have h2 := hk φb (fun x hx => by rw [← hab']; exact hkill x hx) _ hq
    rw [map_sub] at h1 h2
    have h3 := hab' b'
    change φa w = φb w
    rw [sub_eq_zero] at h1 h2
    rw [← h1, ← h2]
    exact h3.symm ▸ rfl
  rw [← ea, ← eb, hφ]

theorem LeafCov2_of : LeafCov2 := by
  intro B W _ _ α I hα hQ U hU T a b h
  have : Etale (Spec.map (CommRingCat.ofHom α)) := HasRingHomProperty.Spec_iff.2 hα
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom α)) := inferInstance
  let π := Spec.map (CommRingCat.ofHom α)
  let l : T ⟶ pullback π π := pullback.lift a b h
  let D := pullback.diagonal π
  let O1 : T.Opens := (a ≫ π) ⁻¹ᵁ U
  let O2 : T.Opens := l ⁻¹ᵁ D.opensRange
  have hP : ∀ {V V' : Scheme.{0}} (j : V' ⟶ V) (k : V ⟶ T),
      (k ≫ a = k ≫ b ∨ ∃ u : V ⟶ (U : Scheme.{0}), u ≫ U.ι = k ≫ a ≫ π) →
      ((j ≫ k) ≫ a = (j ≫ k) ≫ b ∨ ∃ u : V' ⟶ (U : Scheme.{0}), u ≫ U.ι = (j ≫ k) ≫ a ≫ π) := by
    rintro V V' j k (hk | ⟨u, hu⟩)
    · left; rw [Category.assoc, Category.assoc, hk]
    · right; exact ⟨j ≫ u, by rw [Category.assoc, hu, Category.assoc]⟩
  have hcov : TopologicalSpace.IsOpenCover (fun i : Bool => cond i O1 O2) := by
    refine eq_top_iff.2 fun t _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases ht : (a ≫ π) t ∈ U
    · exact ⟨true, ht⟩
    · refine ⟨false, ?_⟩
      have e := agree_at α I hQ U hU T a b h t ht
      obtain ⟨s⟩ : Nonempty (Spec (T.residueField t)) := ⟨IsLocalRing.closedPoint (T.residueField t)⟩
      have hl : T.fromSpecResidueField t ≫ l = (T.fromSpecResidueField t ≫ a) ≫ D := by
        apply pullback.hom_ext
        · simp only [l, D, Category.assoc]
          erw [pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
        · simp only [l, D, Category.assoc]
          erw [pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, e]
      show l t ∈ D.opensRange
      rw [← Scheme.fromSpecResidueField_apply t s, ← Scheme.Hom.comp_apply, hl]
      exact ⟨(T.fromSpecResidueField t ≫ a) s, rfl⟩
  refine etLoc_of_opens T _ hP _ hcov ?_
  rintro (_ | _)
  · left
    have hR : D.opensRange.ι = D.isoOpensRange.inv ≫ D := by
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    have e := morphismRestrict_ι l D.opensRange
    have ea : O2.ι ≫ a = (l ∣_ D.opensRange) ≫ D.isoOpensRange.inv := by
      have := e =≫ pullback.fst π π
      simp only [Category.assoc, hR, D, l, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id] at this
      exact this.symm
    have eb : O2.ι ≫ b = (l ∣_ D.opensRange) ≫ D.isoOpensRange.inv := by
      have := e =≫ pullback.snd π π
      simp only [Category.assoc, hR, D, l, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id] at this
      exact this.symm
    exact ea.trans eb.symm
  · right
    exact ⟨(a ≫ π) ∣_ U, morphismRestrict_ι _ _⟩

end LateralTheory.E.LeafCov2Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibClosedPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf

namespace LateralTheory.E.FibClosedPf

abbrev fm {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    pullback (c ≫ p) (cpt A) ⟶ pullback p (cpt A) :=
  pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp)

def FibQCQS : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A))
  [QuasiCompact c] [QuasiSeparated c], QuasiCompact (fm c p) ∧ QuasiSeparated (fm c p)

def FibStalk : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.map (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s) (𝟙 _)
      ((pullback p (cpt A)).fromSpecStalk s) (fm c p) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem FibClosed_of (hZ : ZLG) (h0 : HZero) (hA : AICAcyc) (hQ : FibQCQS) (hS : FibStalk) : FibClosed := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB
  obtain ⟨_, _⟩ := hQ A c p
  obtain ⟨_, _⟩ := qcqs_of (pullback.snd p (cpt A))
  have hu : IsUnit (q : Γ(pullback p (cpt A), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  exact hZ H q (fm c p) (𝟙 _) hu i (hS H h0 hA q i A hq c p hZs hSs hB)

theorem fm_isPullback {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    IsPullback (fm c p) (pullback.fst (c ≫ p) (cpt A)) (pullback.fst p (cpt A)) c := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p (cpt A)) (h₂₂ := p) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback p (cpt A)).flip
  have e : fm c p ≫ pullback.snd p (cpt A) = pullback.snd (c ≫ p) (cpt A) := by
    unfold fm; rw [pullback.map]; erw [pullback.lift_snd]; simp
  rw [e]
  exact (IsPullback.of_hasPullback (c ≫ p) (cpt A)).flip

theorem fibQCQS : FibQCQS := by
  intro A _ _ Z S c p _ _
  exact ⟨MorphismProperty.of_isPullback (P := @QuasiCompact) (fm_isPullback c p).flip ‹_›,
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (fm_isPullback c p).flip ‹_›⟩

end LateralTheory.E.FibClosedPf
end
end

