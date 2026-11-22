import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0830
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3248
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelSumEqFinsumRegularRationalClasses
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.Regroup

theorem finsum_classes {H : Type} [Group H] (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H),
      ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) :=
  GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets a ha

theorem unfold {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g) (T : Subgroup H) (Γ' : Subgroup G) (hΓ' : ∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g)
    (K : Subgroup G) (u : G → ℂ) (hu : ∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g)
    (h1 : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (h2 : ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom))
    (h3 : ∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
        ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) =
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
      ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) :=
  GlobalTheory.T.unfold_doubleCoset_classSum_to_subgroup ι hι Γ hΓ T Γ' hΓ' K u hu h1 h2 h3

theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU E n) ∧ ∀ x : finU E n, x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x :=
  GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range

theorem finite_classes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n))) :=
  GlobalTheory.T.finite_doubleCoset_rational_productOfLocalLevels

theorem finite_stab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU E n, Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) :=
  GlobalTheory.T.finite_definiteUnitaryRational_inf_conj_level

theorem finite_supp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU E n, {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite :=
  GlobalTheory.T.finite_rationalPoints_support_definiteUnitary_testFunction

theorem separable_of_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU E n) (γ : UE E n), globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable :=
  GlobalTheory.T.separable_charpoly_of_testFunction_ne_zero_regularPlace

end GlobalTheory.BCT.Regroup

namespace GlobalTheory.BCT.Regroup

theorem support_conj_finite {G H : Type} [Group G] [Group H] (ι : H →* G) (Φ : G → ℂ) (x : G)
    (h4 : {γ : H | Φ (x⁻¹ * ι γ * x) ≠ 0}.Finite) (c : H) :
    {δ : H ⧸ twCent (MonoidHom.id H) c | (fun g : G => Φ (g⁻¹ * ι c * g)) ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image (f := fun δ : H ⧸ twCent (MonoidHom.id H) c => Quotient.out δ * c * (Quotient.out δ)⁻¹)
    (h4.subset ?_) ?_
  · rintro _ ⟨δ, hδ, rfl⟩
    show Φ (x⁻¹ * ι (Quotient.out δ * c * (Quotient.out δ)⁻¹) * x) ≠ 0
    have hδ' : Φ (((ι (Quotient.out δ))⁻¹ * x)⁻¹ * ι c * ((ι (Quotient.out δ))⁻¹ * x)) ≠ 0 := hδ
    convert hδ' using 2
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    group
  · intro δ₁ _ δ₂ _ e
    simp only at e
    rw [← Quotient.out_eq δ₁, ← Quotient.out_eq δ₂]
    apply QuotientGroup.eq.2
    change (Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂)
    calc (Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c
        = (Quotient.out δ₁)⁻¹ * (Quotient.out δ₂ * c * (Quotient.out δ₂)⁻¹) * Quotient.out δ₂ := by group
      _ = (Quotient.out δ₁)⁻¹ * (Quotient.out δ₁ * c * (Quotient.out δ₁)⁻¹) * Quotient.out δ₂ := by rw [e]
      _ = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂) := by group

theorem regroup_abstract {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g) (K : Subgroup G) (Φ : G → ℂ) (ψ : H → ℂ)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (k⁻¹ * g * k) = Φ g) (hψ : ∀ a b, ψ (b⁻¹ * a * b) = ψ a)
    (h1 : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (h2 : ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom))
    (h4 : ∀ x : G, {γ : H | Φ (x⁻¹ * ι γ * x) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
        ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ =
    ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep *
      ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ twCent (MonoidHom.id G) (ι c.rep) : Subgroup G) : Set G) (K : Set G),
        ((Nat.card ↥((Γ ⊓ twCent (MonoidHom.id G) (ι c.rep)) ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
          Φ ((Quotient.out q)⁻¹ * ι c.rep * Quotient.out q) := by
  classical
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
  set D : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → TwCl (MonoidHom.id H) → ℂ := fun q c =>
    ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
      Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) with hD

  have s1 : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ = ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep * D q c := by
    intro q
    rw [finsum_classes _ ((h4 (Quotient.out q)).subset fun γ hγ => left_ne_zero_of_mul hγ)]
    refine finsum_congr fun c => ?_
    rw [hD, mul_finsum]
    refine finsum_congr fun δ => ?_
    have : ψ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = ψ c.rep := by
      simpa using hψ c.rep (Quotient.out δ)⁻¹
    rw [this, mul_comm]

  have hsupp : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      (Function.support fun c : TwCl (MonoidHom.id H) => ψ c.rep * D q c).Finite := by
    intro q
    refine ((h4 (Quotient.out q)).image (fun γ => (Quot.mk _ γ : TwCl (MonoidHom.id H)))).subset ?_
    intro (c : TwCl (MonoidHom.id H)) hc
    have hc' : D q c ≠ 0 := right_ne_zero_of_mul hc
    obtain ⟨δ, hδ⟩ : ∃ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
        Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hc' (by rw [hD]; simp only; rw [finsum_congr hn]; simp)
    refine ⟨_, hδ, ?_⟩
    change Quot.mk _ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = c
    exact (Quot.sound ⟨Quotient.out δ, by simp [mul_assoc]; rfl⟩).trans (Quot.out_eq c)
  simp_rw [s1]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [mul_finsum]
  rw [← finsum_sum_comm]
  · refine finsum_congr fun c => ?_
    have e2 := unfold ι hι Γ hΓ (twCent (MonoidHom.id H) c.rep) (Γ ⊓ twCent (MonoidHom.id G) (ι c.rep))
      (fun g => by
        constructor
        · rintro ⟨hg, hc⟩
          obtain ⟨h, rfl⟩ := (hΓ g).1 hg
          refine ⟨h, hι ?_, rfl⟩
          change ι h * ι c.rep = ι c.rep * ι h at hc
          change ι (h * c.rep) = ι (c.rep * h)
          rw [map_mul, map_mul, hc]
        · rintro ⟨t, ht, rfl⟩
          refine ⟨(hΓ _).2 ⟨t, rfl⟩, ?_⟩
          change ι t * ι c.rep = ι c.rep * ι t
          have ht' : t * c.rep = c.rep * t := ht
          rw [← map_mul, ht', map_mul])
      K (fun g => Φ (g⁻¹ * ι c.rep * g))
      (fun t ht k hk g => by
        have ht' : t * c.rep = c.rep * t := ht
        simp only [_root_.mul_inv_rev]
        have : (k⁻¹ * (g⁻¹ * (ι t)⁻¹) * ι c.rep * (ι t * g * k)) = k⁻¹ * (g⁻¹ * ι c.rep * g) * k := by
          have : (ι t)⁻¹ * ι c.rep * ι t = ι c.rep := by
            rw [← map_inv, ← map_mul, ← map_mul, mul_assoc, ← ht', inv_mul_cancel_left]
          calc _ = k⁻¹ * (g⁻¹ * ((ι t)⁻¹ * ι c.rep * ι t) * g) * k := by group
            _ = _ := by rw [this]
        rw [this, hΦ k hk])
      h1 h2 (fun x => support_conj_finite ι Φ x (h4 x) c.rep)
    rw [← mul_finsum, ← e2, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hD]
    simp only
    rw [mul_left_comm]
    congr 2
    refine finsum_congr fun δ => ?_
    congr 1
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    group
  · intro q _
    exact (hsupp q).subset fun c hc => right_ne_zero_of_mul hc

end GlobalTheory.BCT.Regroup

namespace GlobalTheory.BCT.Regroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_conj {G : Type} [Group G] (U : Subgroup G) (k : U) (y : G) :
    toSub U ((k : G)⁻¹ * y * k) = k⁻¹ * toSub U y * k := by
  unfold toSub
  by_cases hy : y ∈ U
  · rw [dif_pos hy, dif_pos (mul_mem (mul_mem (inv_mem k.2) hy) k.2)]
    ext
    simp
  · rw [dif_neg hy, dif_neg]
    · simp
    · intro h
      apply hy
      have := mul_mem (mul_mem k.2 h) (inv_mem k.2)
      simpa [mul_assoc] using this

theorem globFn_conj (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, IsHecke (K' w) (f w)) (k : finU E n) (hk : k ∈ globLev S K') (g : finU E n) :
    globFn S f (k⁻¹ * g * k) = globFn S f g := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  have hkw : cLoc w k.1 ∈ (K' w).map (UL n w).subtype := by
    have h1 := Subgroup.mem_iInf.1 hk w
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 hw)
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hkw
  have e2 : cLoc w (k⁻¹ * g * k).1 = ((k' : UL n w) : GLw n w)⁻¹ * cLoc w g.1 * (k' : GLw n w) := by
    have e' : (k' : GLw n w) = cLoc w k.1 := e
    rw [e']
    simp
  rw [e2, toSub_conj, ((hf w).2 k' hk' _).2, ((hf w).2 k'⁻¹ (inv_mem hk') _).1]

theorem chW_conj (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    chW lam (b⁻¹ * a * b).1.val.charpoly = chW lam a.1.val.charpoly := by
  congr 1
  have : (b⁻¹ * a * b).1.val = (b.1.val)⁻¹ * a.1.val * b.1.val := by
    simp [Matrix.coe_units_inv]
  rw [this]
  have h := Matrix.charpoly_units_conj (b.1)⁻¹ a.1.val
  simpa [Matrix.coe_units_inv] using h

theorem kernSum_eq_finsum_classes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → kernSum S lam K' f = ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then chW lam c.rep.1.val.charpoly * clsSum S K' f c.rep else 0 := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  obtain ⟨hmul, hinj, hmem⟩ := finPt_props E n
  let ι : UE E n →* finU E n := MonoidHom.mk' finPt hmul
  have key : ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n)),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly =
    ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), chW lam c.rep.1.val.charpoly *
      ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU E n)) : Set (finU E n))
        (globLev S K' : Set (finU E n)),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) :=
    regroup_abstract ι hinj (ratFinU E n) hmem (globLev S K') (globFn S f) (fun γ => chW lam γ.1.val.charpoly)
      (globFn_conj S K' f hf.1) (chW_conj lam) (finite_classes E hU n hn S hS K' hK) (finite_stab E hU n hn S hS K' hK)
      (finite_supp E hU n hn S hS K' hK f hf)
  obtain ⟨w, hw, hsep⟩ := hreg
  unfold kernSum
  rw [key, mul_finsum]
  refine finsum_congr fun c => ?_
  split_ifs with hc
  · rw [clsSum]
    ring
  · have h0 : ∀ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU E n)) :
        Set (finU E n)) (globLev S K' : Set (finU E n)),
        globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) = 0 := fun q => by
      by_contra h
      exact hc (separable_of_globFn_ne_zero E n S K' f hf w hw hsep _ _ h)
    simp [h0]

end GlobalTheory.BCT.Regroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.LatDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def actZ (Dw : Datum H) : 𝓞 E →+* Module.End ℤ Dw.La := (Algebra.lsmul ℤ ℤ Dw.La).toRingHom

theorem actZ_apply (Dw : Datum H) (o : 𝓞 E) :
    actZ Dw o = (LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ :=
  LinearMap.ext fun _ => rfl

theorem finrank_eig (Dw : Datum H) [Module.Finite ℤ Dw.La] [Module.Free ℤ Dw.La] {K : Type} [Field K]
    [Algebra K ℂ] (V : ValuationSubring K) (σ : 𝓞 E →+* V) :
    Module.finrank V (EigenSplit.eigenSub (EigenSplit.baseChangeAction V (actZ Dw)) σ) = Dw.p + Dw.q := by
  have : FaithfulSMul V K := (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective V K)
  have : Module.Flat V K := EigenSplit.flat_of_valuationRing V K
  have hF := EigenSplit.finrank_eigenSub_of_flat (R := V) (R' := K) (ρ := EigenSplit.baseChangeAction V (actZ Dw))
    (ρ' := EigenSplit.baseChangeAction K (actZ Dw)) (f := EigenSplit.extendTensor ℤ V K Dw.La)
    (EigenSplit.extendTensor_equivariant V K (actZ Dw)) (EigenSplit.isBaseChange_extendTensor ℤ V K Dw.La) σ
  have hC := EigenSplit.finrank_eigenSub_of_flat (R := K) (R' := ℂ) (ρ := EigenSplit.baseChangeAction K (actZ Dw))
    (ρ' := EigenSplit.baseChangeAction ℂ (actZ Dw)) (f := EigenSplit.extendTensor ℤ K ℂ Dw.La)
    (EigenSplit.extendTensor_equivariant K ℂ (actZ Dw)) (EigenSplit.isBaseChange_extendTensor ℤ K ℂ Dw.La)
    ((algebraMap V K).comp σ)
  have hT := TensorDet.finrank_eigenSub (E := E) (k := ℂ) (O := ℤ) (M := Dw.La)
    ((algebraMap K ℂ).comp ((algebraMap V K).comp σ)) (RingHom.ext_int _ _)
  have e : TensorDet.rightAction ℂ ℤ (𝓞 E) Dw.La = EigenSplit.baseChangeAction ℂ (actZ Dw) := rfl
  rw [e, hC, hF, Dw.rank] at hT
  exact hT

end GlobalTheory.FlatModel.LatDual

namespace GlobalTheory.FlatModel.LatDual

theorem latSt : LatSt := by
  intro E _ _ _ H Dw l c W p hp hW τ
  classical
  obtain ⟨N, ⟨a⟩⟩ : ∃ k : ℕ, Nonempty (Module.Basis (Fin k) ℤ Dw.La) := by
    haveI := Dw.fin
    haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
    haveI : Module.IsTorsionFree ℤ Dw.La :=
      Function.Injective.moduleIsTorsionFree Dw.EF Dw.unimod.1 (fun r x => map_smul _ r x)
    haveI : Module.Free ℤ Dw.La := Module.free_of_finite_type_torsion_free'
    exact ⟨_, ⟨Module.finBasis ℤ Dw.La⟩⟩
  haveI : Module.Free ℤ Dw.La := Module.Free.of_basis a
  haveI : Module.Finite ℤ Dw.La := Module.Finite.of_basis a
  set σ : 𝓞 E →+* c.V W := embV c W (conjEmb τ.1) with hσ
  set K := EigenSplit.eigenSub (EigenSplit.baseChangeAction (c.V W) (actZ Dw)) σ with hK
  haveI : Module.Free (c.V W) K := EigenSplit.free_eigenSub_of_valuationRing _ _
  haveI : Module.Finite (c.V W) K := EigenSplit.finite_eigenSub_of_valuationRing _ _
  have hrk : Fintype.card (Ind Dw τ.1) = Module.finrank (c.V W) K := by
    rw [hK, finrank_eig, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
      GlobalTheory.ShFam.Pad.AdmExist.mult_add_mult_conj]
  let b : Module.Basis (Ind Dw τ.1) (c.V W) K := (Module.finBasis (c.V W) K).reindex (Fintype.equivFinOfCardEq hrk).symm
  obtain ⟨Q, hQ⟩ := EigenSplit.exists_isCompl_eigenSub_of_valuationRing (EigenSplit.baseChangeAction (c.V W) (actZ Dw)) σ
  let pr := Submodule.linearProjOfIsCompl K Q hQ
  let f : Ind Dw τ.1 → (c.V W ⊗[ℤ] Dw.La →ₗ[c.V W] c.V W) := fun i => (b.coord i).comp pr
  have hf : ∀ i j, f i (b j) = if i = j then 1 else 0 := by
    intro i j
    show b.coord i (pr (b j)) = _
    rw [show pr (b j) = b j from Submodule.linearProjOfIsCompl_apply_left hQ (b j), Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  choose y hy using fun m' : Fin N => Dw.unimod.2 (a.coord m')
  let cc : Fin N → Fin N → ℤ := fun m' m => a.repr (y m') m
  have hcc : ∀ m' k, ∑ m, cc m' m * Dw.EF (a m) (a k) = if m' = k then 1 else 0 := by
    intro m' k
    have h0 : Dw.EF (y m') (a k) = ∑ m, cc m' m * Dw.EF (a m) (a k) := by
      calc Dw.EF (y m') (a k) = Dw.EF (∑ m, a.repr (y m') m • a m) (a k) := by rw [a.sum_repr]
        _ = ∑ m, cc m' m * Dw.EF (a m) (a k) := by
          simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, cc]
    rw [← h0, hy, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  let tb := Algebra.TensorProduct.basis (c.V W) a
  let T : Ind Dw τ.1 → Fin N → c.V W := fun j m => tb.repr (b j : c.V W ⊗[ℤ] Dw.La) m
  let S : Ind Dw τ.1 → Fin N → c.V W := fun i m => ∑ m', f i (1 ⊗ₜ a m') * (cc m' m : c.V W)
  have hT : ∀ j, ∑ m, T j m ⊗ₜ[ℤ] a m = (b j : c.V W ⊗[ℤ] Dw.La) := by
    intro j
    conv_rhs => rw [← tb.sum_repr (b j : c.V W ⊗[ℤ] Dw.La)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have hS : ∀ i k, ∑ m, S i m * ((Dw.EF (a m) (a k) : ℤ) : c.V W) = f i (1 ⊗ₜ a k) := by
    intro i k
    simp only [S, Finset.sum_mul]
    rw [Finset.sum_comm]
    have e : ∀ m', ∑ m, f i (1 ⊗ₜ a m') * (cc m' m : c.V W) * ((Dw.EF (a m) (a k) : ℤ) : c.V W)
        = f i (1 ⊗ₜ a m') * (if m' = k then 1 else 0) := by
      intro m'
      have h2 := congrArg (fun z : ℤ => (z : c.V W)) (hcc m' k)
      simp only [Int.cast_sum, Int.cast_mul] at h2
      simp_rw [_root_.mul_assoc, ← Finset.mul_sum, h2]
      split_ifs <;> simp
    simp_rw [e, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨N, a, T, S, ?_, ?_, ?_⟩
  · intro i o
    have hm := EigenSplit.mem_eigenSub.1 (b i).2 o
    rw [EigenSplit.baseChangeAction_apply, actZ_apply] at hm
    have e1 : ∑ m, T i m ⊗ₜ[ℤ] (o • a m)
        = ((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange (c.V W) (∑ m, T i m ⊗ₜ[ℤ] a m) := by
      simp [map_sum, LinearMap.baseChange_tmul]
    rw [e1, hT, hm, ← hT, Finset.smul_sum]
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  · intro i j
    have e2 : ∑ m, ∑ m', S i m * T j m' * ((Dw.EF (a m) (a m') : ℤ) : c.V W) = f i (b j) := by
      rw [Finset.sum_comm]
      simp_rw [mul_comm (S i _) (T j _), _root_.mul_assoc, ← Finset.mul_sum, hS]
      rw [← hT j, map_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      have e3 : T j m' ⊗ₜ[ℤ] a m' = T j m' • ((1 : c.V W) ⊗ₜ[ℤ] a m') := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e3, map_smul, smul_eq_mul]
    rw [e2, hf]
  · intro x hx
    have hxK : x ∈ K := EigenSplit.mem_eigenSub.2 fun o => by
      rw [EigenSplit.baseChangeAction_apply, actZ_apply]; exact hx o
    have e' : x = ∑ i, b.repr ⟨x, hxK⟩ i • (b i : c.V W ⊗[ℤ] Dw.La) := by
      conv_lhs => rw [show x = ((⟨x, hxK⟩ : K) : c.V W ⊗[ℤ] Dw.La) from rfl, ← b.sum_repr ⟨x, hxK⟩]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [e']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hT i⟩)

end GlobalTheory.FlatModel.LatDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
namespace GlobalTheory.Mix

theorem logSec_intg_proj : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro hP F _ X _ _ p σ D hproj hdim L M s hs
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hprojY, hdimY, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p D hproj hdim ⊥ (fun h => h)
  haveI : Smooth (π ≫ p) := SmoothOfRelativeDimension.smooth D (π ≫ p)
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
  obtain ⟨s', hz, hn, -⟩ := GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities F X Y p (π ≫ p) σ π rfl M s
  have hs' : genericPoint Y ∈ nonzeroLocus s' := by
    rw [hz]; show π (genericPoint Y) ∈ nonzeroLocus s; rw [hgen]; exact hs
  have hsmooth := GlobalTheory.T.integrable_logNormSection_mixedChernForms F Y (π ≫ p) σ D hprojY hsm (fun i => (L i).pull π rfl) (M.pull π rfl) s' hs'
  have hmeas := (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1
  have hpush := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ D hproj hdim hprojY π rfl hgen (by rw [hdeg]; exact one_ne_zero) L (M.logSec s) hmeas).1
  refine hpush.1 ?_
  have hfun : (fun y => M.logSec s (ptMap π rfl σ y)) = (M.pull π rfl).logSec s' := by
    funext y; simp only [MLine.logSec]; rw [hn y]
  rw [hfun]; exact hsmooth

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFrobeniusKernelIdealOfZeroDifferential
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerPrim

theorem mem_frobKerIdeal_of_cobOne (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H] (b : H)
    (_hb : counit (R := K) b = 0) (hd : dUnit K b = 0)
    (hc : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H))
      (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0) :
    b ∈ frobKerIdeal p K H := by
  haveI := FrobKerOrder.isHopfIdeal p K H
  set J := frobKerIdeal p K H with hJ
  let π : H →ₐc[K] H ⧸ J := Bialgebra.Quotient.mkBialgHom J
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsCocomm K (H ⧸ J) := by
    constructor
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπ y
    have h1 := pullTwo_comul π x
    simp only [LinearMap.comp_apply]
    rw [← h1]
    simp only [pullbackTwo]
    have h2 := TensorProduct.map_comm (π : H →ₗ[K] H ⧸ J) (π : H →ₗ[K] H ⧸ J) (comul x)
    rw [comm_comul] at h2
    exact h2.symm
  have hpow : ∀ a ∈ augIdeal K (H ⧸ J), a ^ p = 0 := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    have hx : x ∈ augIdeal K H := ha
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal hx)
  have hc' : cobOne K (H ⧸ J) (π b) = 0 := by
    rw [← pullTwo_cobOne]
    exact hc
  have hd' : dUnit K (π b) = 0 := by
    rw [← cotMap_d, hd, map_zero]
  have h0 := GlobalTheory.T.hopf_height_one_primitive_eq_zero_of_zero_differential p K (H ⧸ J) hpow (π b) hc' hd'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

end GlobalTheory.PDiv.FrobKerPrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySiegelFamilyOfDivisorLevelSamePrimesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_siegelFamily_of_divisor_level_same_primes : ∀ h n N : ℕ, 3 ≤ n → Odd N → n ∣ N → (∃ a, N ∣ n ^ a) → Nonempty (SFam h N (zetaAway N)) → Nonempty (SFam h n (zetaAway n)) := by
  first | exact @GlobalTheory.SiegLev.sFam_down | exact GlobalTheory.SiegLev.sFam_down | (intros; apply GlobalTheory.SiegLev.sFam_down <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointsSimilitudeGLProductBijectiveStatement
section
open GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicPoints_similitude_GL_product_bijective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.bijective_locP) | (exact GlobalTheory.LKTrip.HTGroup.bijective_locP) | (intros; apply GlobalTheory.LKTrip.HTGroup.bijective_locP  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QexpansionOnAllComponentsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qexpansion_on_all_components : GlobalTheory.Published.DelignePappasModel → GlobalTheory.Published.HilbertQExpansion → GlobalTheory.RealMult.QExpansionOnAll := by
  first | exact @GlobalTheory.RealMult.qExpansionOnAll_of_model | exact GlobalTheory.RealMult.qExpansionOnAll_of_model | (intros; apply GlobalTheory.RealMult.qExpansionOnAll_of_model <;> assumption)
end

