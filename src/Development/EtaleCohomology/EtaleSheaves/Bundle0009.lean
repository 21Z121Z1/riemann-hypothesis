import Development.EtaleCohomology.EtaleSheaves.Bundle0004
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCGoodPf
section
open LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LCGoodPf

theorem closed_empty {C : Type} [CommRing C] {J : Ideal C} (hJ : J ≤ Ideal.jacobson ⊥)
    (Z : Set (PrimeSpectrum C)) (hZ : IsClosed Z)
    (h : ∀ z : PrimeSpectrum (C ⧸ J), PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∉ Z) : Z = ∅ := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  by_cases hI : I = ⊤
  · subst hI; simp
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  exfalso
  have hJM : J ≤ M := le_trans hJ (sInf_le ⟨bot_le, hM⟩)
  have hp : (⟨M, hM.isPrime⟩ : PrimeSpectrum C) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ M := by rw [Ideal.mk_ker]; exact hJM
    have := hM.isPrime
    have hpr : (M.map (Ideal.Quotient.mk J)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    refine ⟨⟨M.map (Ideal.Quotient.mk J), hpr⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.map _ M) = M
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_eq_left.2 ?_
    rw [← RingHom.ker_eq_comap_bot]; exact hker
  obtain ⟨z, hz⟩ := hp
  apply h z
  rw [hz]
  exact hIM

theorem lcMap_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Y : Type}
    (φ : LocallyConstant (PrimeSpectrum A) Y) (z : PrimeSpectrum B) :
    lcMap f φ z = φ (PrimeSpectrum.comap f z) := rfl

theorem isClosed_ne {X Y : Type} [TopologicalSpace X] (a b : LocallyConstant X Y) :
    IsClosed {x | a x ≠ b x} := by
  have : IsLocallyConstant (fun x => (a x = b x : Prop)) :=
    IsLocallyConstant.comp₂ a.isLocallyConstant b.isLocallyConstant (fun u v => (u = v : Prop))
  have h2 := this.isClosed_fiber False
  convert h2 using 1
  ext x; simp

theorem LCGood_of : LCGood := by
  intro C _ J hG Y
  obtain ⟨hJ, hlift⟩ := hG
  constructor
  · intro a b hab
    have hZ := closed_empty hJ _ (isClosed_ne a b) (fun z hz => hz (by
      have := congrArg (fun φ => φ z) hab
      simpa [lcMap_apply] using this))
    ext x
    by_contra hx
    have : x ∈ ({x | a x ≠ b x} : Set _) := hx
    rw [hZ] at this; exact this
  · intro ψ

    have hU : ∀ y : Y, ∃ U : Set (PrimeSpectrum C), IsClopen U ∧
        PrimeSpectrum.comap (Ideal.Quotient.mk J) ⁻¹' U = ψ ⁻¹' {y} := by
      intro y
      obtain ⟨e, he, hF⟩ := PrimeSpectrum.isClopen_iff.1 (ψ.isLocallyConstant.isClopen_fiber y)
      obtain ⟨x, hx, hxe⟩ := hlift e he
      refine ⟨PrimeSpectrum.basicOpen x, PrimeSpectrum.isClopen_iff.2 ⟨x, hx, rfl⟩, ?_⟩
      have hF' : ψ ⁻¹' {y} = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum (C ⧸ J))) := hF
      rw [hF', ← hxe]
      ext p
      simp
    choose U hUc hUp using hU
    have hmem : ∀ z y, PrimeSpectrum.comap (Ideal.Quotient.mk J) z ∈ U y ↔ ψ z = y := by
      intro z y
      have := congrArg (fun s => z ∈ s) (hUp y)
      simpa using this
    have hcover : ∀ x, ∃ y, x ∈ U y := by
      have hE := closed_empty hJ (⋃ y, U y)ᶜ
        (isOpen_iUnion (fun y => (hUc y).isOpen)).isClosed_compl
        (fun z hz => hz (Set.mem_iUnion.2 ⟨ψ z, (hmem z _).2 rfl⟩))
      intro x
      by_contra hx
      push Not at hx
      have : x ∈ (⋃ y, U y)ᶜ := by simpa using hx
      rw [hE] at this
      exact this
    have huniq : ∀ x y y', x ∈ U y → x ∈ U y' → y = y' := by
      intro x y y' h1 h2
      by_contra hne
      have := closed_empty hJ (U y ∩ U y') ((hUc y).isClosed.inter (hUc y').isClosed)
        (fun z hz => hne (((hmem z y).1 hz.1).symm.trans ((hmem z y').1 hz.2)))
      have hx : x ∈ U y ∩ U y' := ⟨h1, h2⟩
      rw [this] at hx; exact hx
    classical
    let g : PrimeSpectrum C → Y := fun x => Classical.choose (hcover x)
    have hg : ∀ x y, g x = y ↔ x ∈ U y := by
      intro x y
      constructor
      · rintro rfl; exact Classical.choose_spec (hcover x)
      · intro h; exact huniq x _ _ (Classical.choose_spec (hcover x)) h
    have hgl : IsLocallyConstant g := by
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro y
      have : g ⁻¹' {y} = U y := by ext x; simp [hg]
      rw [this]; exact (hUc y).isOpen
    refine ⟨⟨g, hgl⟩, ?_⟩
    ext z
    rw [lcMap_apply]
    exact (hg _ _).2 ((hmem z _).2 rfl)

end LateralTheory.E.LCGoodPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCSplitPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LCSplitPf
open LateralTheory.E.t_E1Cut

def Idem : Prop := ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R] (φ : LocallyConstant (PrimeSpectrum R) (ZMod q)),
  ∃ ε : ZMod q → R, CompleteOrthogonalIdempotents ε ∧ ∀ (p : PrimeSpectrum R) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal

def Torsor : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q)) (ε : ZMod q → Localization.Away (f * g)),
  CompleteOrthogonalIdempotents ε → (∀ (p : PrimeSpectrum (Localization.Away (f * g))) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal) →
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra S C), Algebra.Etale S C ∧ Module.Finite S C ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) ∧
    (Nonempty (C →ₐ[S] S) → ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b)

theorem LCSplit_of_idem (hF : FinEtSection) (hI : Idem) (hT : Torsor) : LCSplit := by
  intro q _ S _ hS f g hfg φ
  obtain ⟨ε, hε, hφ⟩ := hI q _ φ
  obtain ⟨C, _, _, hEt, hFin, hSurj, hsec⟩ := hT q S f g hfg φ ε hε hφ
  exact hsec (hF S C hS hSurj)

theorem idem_of : Idem := by
  intro q _ R _ φ
  classical
  let E := fun c : ZMod q => PrimeSpectrum.isIdempotentElemEquivClopens (R := R) |>.symm
    ⟨{x | φ x = c}, φ.isLocallyConstant.isClopen_fiber c⟩
  have hB : ∀ c, PrimeSpectrum.basicOpen (E c).1 = ⟨{x | φ x = c}, (φ.isLocallyConstant.isClopen_fiber c).isOpen⟩ :=
    fun c => PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _
  have hmem : ∀ (p : PrimeSpectrum R) c, φ p = c ↔ (E c).1 ∉ p.asIdeal := by
    intro p c
    have := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) => p ∈ U) (hB c)
    simp only [PrimeSpectrum.mem_basicOpen] at this
    exact (this.to_iff.trans (by rfl)).symm
  refine ⟨fun c => (E c).1, ?_, hmem⟩
  have hid : ∀ c, IsIdempotentElem (E c).1 := fun c => (E c).2
  have horth : OrthogonalIdempotents (fun c => (E c).1) := by
    refine ⟨hid, ?_⟩
    intro c d hcd
    apply IsIdempotentElem.eq_zero_of_isNilpotent ((hid c).mul (hid d))
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    by_contra h
    have hc : (E c).1 ∉ J := fun hc => h (J.mul_mem_right _ hc)
    have hd : (E d).1 ∉ J := fun hd => h (J.mul_mem_left _ hd)
    exact hcd (((hmem ⟨J, hJ⟩ c).2 hc).symm.trans ((hmem ⟨J, hJ⟩ d).2 hd))
  refine CompleteOrthogonalIdempotents.of_prod_one_sub horth ?_
  have hP : IsIdempotentElem (∏ c, (1 - (E c).1)) := by
    classical
    induction (Finset.univ : Finset (ZMod q)) using Finset.induction_on with
    | empty => simpa using IsIdempotentElem.one
    | insert a s ha ih => rw [Finset.prod_insert ha]; exact (hid a).one_sub.mul ih
  apply IsIdempotentElem.eq_zero_of_isNilpotent hP
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  rw [Ideal.IsPrime.prod_mem_iff]
  refine ⟨φ ⟨J, hJ⟩, Finset.mem_univ _, ?_⟩
  have hn : (E (φ ⟨J, hJ⟩)).1 ∉ J := (hmem ⟨J, hJ⟩ _).1 rfl
  have h0 : (E (φ ⟨J, hJ⟩)).1 * (1 - (E (φ ⟨J, hJ⟩)).1) ∈ J := by
    rw [mul_sub, mul_one, (hid _).eq, sub_self]; exact J.zero_mem
  exact (hJ.mem_or_mem h0).resolve_left hn

theorem LCSplit_of (hF : FinEtSection) (hT : Torsor) : LCSplit := LCSplit_of_idem hF idem_of hT

section Conc
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

def twist (hε : CompleteOrthogonalIdempotents ε) : (ZMod q → A) →+* (ZMod q → A) where
  toFun z k := ∑ c, ε c * z (k + c)
  map_one' := by funext k; simp [hε.complete]
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_mul' x y := by
    funext k
    simp only [Pi.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [show ε c * x (k + c) * (ε c * y (k + c)) = (ε c * ε c) * (x (k + c) * y (k + c)) by ring, (hε.idem c).eq]
    · intro d _ hdc
      rw [show ε c * x (k + c) * (ε d * y (k + d)) = (ε c * ε d) * (x (k + c) * y (k + d)) by ring, hε.ortho (Ne.symm hdc), zero_mul]
    · simp
end Conc

section Tor
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}

abbrev Amb (q : ℕ) := (ZMod q → Localization.Away f) × (ZMod q → Localization.Away g)

def h1 : Amb f g q →+* (ZMod q → Localization.Away (f * g)) :=
  Pi.ringHom fun k => (rL f g).comp ((Pi.evalRingHom _ k).comp (RingHom.fst _ _))

def h2 (hε : CompleteOrthogonalIdempotents ε) : Amb f g q →+* (ZMod q → Localization.Away (f * g)) :=
  (twist hε).comp (Pi.ringHom fun k => (rR f g).comp ((Pi.evalRingHom _ k).comp (RingHom.snd _ _)))

def Tor (hε : CompleteOrthogonalIdempotents ε) : Subring (Amb f g q) := RingHom.eqLocus (h1 f g) (h2 f g hε)

def torMap (hε : CompleteOrthogonalIdempotents ε) : S →+* Tor f g hε :=
  RingHom.codRestrict (RingHom.prod ((Pi.constRingHom (ZMod q) _).comp (algebraMap S _))
    ((Pi.constRingHom (ZMod q) _).comp (algebraMap S _))) (Tor f g hε) (by
    intro s
    show h1 f g _ = h2 f g hε _
    funext k
    change rL f g (algebraMap S _ s) = ∑ c, ε c * rR f g (algebraMap S _ s)
    unfold rL rR
    rw [IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq, ← Finset.sum_mul, hε.complete, one_mul])
end Tor

def TorEt : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Algebra.Etale S (Tor f g hε) ∧ Module.Finite S (Tor f g hε) ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap S (Tor f g hε)))

def TorSec : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q)) (ε : ZMod q → Localization.Away (f * g))
  (hε : CompleteOrthogonalIdempotents ε), (∀ (p : PrimeSpectrum (Localization.Away (f * g))) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal) →
  letI := (torMap f g hε).toAlgebra
  Nonempty (Tor f g hε →ₐ[S] S) → ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b

theorem torsor_of (hE : TorEt) (hS : TorSec) : Torsor := by
  intro q _ S _ f g hfg φ ε hε hφ
  letI := (torMap f g hε).toAlgebra
  obtain ⟨h1, h2, h3⟩ := hE q S f g hfg ε hε
  exact ⟨Tor f g hε, inferInstance, (torMap f g hε).toAlgebra, h1, h2, h3, hS q S f g hfg φ ε hε hφ⟩

theorem LCSplit_of_tor (hF : FinEtSection) (hE : TorEt) (hS : TorSec) : LCSplit := LCSplit_of hF (torsor_of hE hS)

end LateralTheory.E.LCSplitPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafChartPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafChartPf

def LeafChartAff : Prop := ∀ {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)] (x : X), x ∈ Set.range ι →
  ∀ W : X.Opens, x ∈ W → ∃ (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (I : Ideal B),
    Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B ∧
    Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) ∧
    ∃ (j : Spec (CommRingCat.of B) ⟶ X) (_ : IsOpenImmersion j), x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧
      ∀ y : Spec (CommRingCat.of B), j y ∈ Set.range ι ↔ I ≤ (show PrimeSpectrum B from y).asIdeal

def LeafChartAway : Prop := ∀ {X : Scheme.{0}} (Y : Set X) (B : Type) [CommRing B] (j : Spec (CommRingCat.of B) ⟶ X)
  [IsOpenImmersion j] (I : Ideal B) (g : B),
  (∀ y : Spec (CommRingCat.of B), j y ∈ Y ↔ I ≤ (show PrimeSpectrum B from y).asIdeal) →
  ∃ (j' : Spec (CommRingCat.of (Localization.Away g)) ⟶ X) (_ : IsOpenImmersion j'), Set.range j' ⊆ Set.range j ∧
    (∀ y : Spec (CommRingCat.of B), g ∉ (show PrimeSpectrum B from y).asIdeal → j y ∈ Set.range j') ∧
    ∀ y' : Spec (CommRingCat.of (Localization.Away g)), j' y' ∈ Y ↔
      I.map (algebraMap B (Localization.Away g)) ≤ (show PrimeSpectrum (Localization.Away g) from y').asIdeal

theorem LeafChart_of (hR : LateralTheory.E.t_E6Cut.LeafChartRing) (hA : LeafChartAff) (hW : LeafChartAway) :
    LateralTheory.E.t_E6Cut.LeafChart := by
  intro X Z S p ι _ d e _ _ x hx W hxW
  obtain ⟨A, B, _, _, _, I, h1, h2, j, _, ⟨y0, rfl⟩, hjW, hj⟩ := hA p ι d e x hx W hxW
  have hI : I ≤ (show PrimeSpectrum B from y0).asIdeal := (hj y0).1 hx
  obtain ⟨g, hg, C, _, φ, het, heq⟩ :=
    hR d e A B I h1 h2 (show PrimeSpectrum B from y0).asIdeal inferInstance hI
  obtain ⟨j', hj', hsub, hcov, hiff⟩ := hW (Set.range ι) B j I g hj
  refine ⟨Localization.Away g, C, inferInstance, inferInstance, j', hj', φ, het, hcov y0 hg,
    hsub.trans hjW, fun y' => ?_⟩
  rw [hiff y', heq]

end LateralTheory.E.LeafChartPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafChartRingPf
section
noncomputable section

namespace LateralTheory.E.LeafChartRingPf

open MvPolynomial

def coordMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d e : ℕ} (g : B)
    (y : Fin e → B) (t : Fin d → B) : MvPolynomial (Fin d) (MvPolynomial (Fin e) A) →+* Localization.Away g :=
  MvPolynomial.eval₂Hom (MvPolynomial.aeval (fun k => algebraMap B (Localization.Away g) (y k))).toRingHom
    (fun j => algebraMap B (Localization.Away g) (t j))

def LeafCoords : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ g ∉ P, ∃ (t : Fin d → B) (y : Fin e → B),
    I.map (algebraMap B (Localization.Away g)) = Ideal.span (Set.range fun j => algebraMap B (Localization.Away g) (t j)) ∧
    LinearIndependent (Localization.Away g) (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j)))) ∧
    Submodule.span (Localization.Away g) (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j))))) = ⊤

def LeafJacobian : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ),
  Algebra.IsStandardSmoothOfRelativeDimension n A B → ∀ (g : B) (t : Fin d → B) (y : Fin e → B),
    LinearIndependent (Localization.Away g) (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j)))) →
    Submodule.span (Localization.Away g) (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j))))) = ⊤ →
    (coordMap (A := A) g y t).Etale

theorem varIdeal_coordMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d e : ℕ} (g : B)
    (y : Fin e → B) (t : Fin d → B) :
    LateralTheory.E.t_E6Cut.varIdeal (coordMap (A := A) g y t) =
      Ideal.span (Set.range fun j => algebraMap B (Localization.Away g) (t j)) := by
  unfold LateralTheory.E.t_E6Cut.varIdeal coordMap
  simp

theorem LeafChartRing_of (hC : LeafCoords) (hJ : LeafJacobian) : LateralTheory.E.t_E6Cut.LeafChartRing := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨g, hg, t, y, hI, hli, hsp⟩ := hC d e A B I hB hBI P hP hIP
  refine ⟨g, hg, MvPolynomial (Fin e) A, inferInstance, coordMap (A := A) g y t,
    hJ d e A B (e + d) hB g t y hli hsp, ?_⟩
  rw [varIdeal_coordMap, hI]

end LateralTheory.E.LeafChartRingPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafChernPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.ChernPf

theorem cast_rfl {q : ℕ} {E : Spc} {n i : ℤ} (x : Ht q E n i) (h1 : n = n) (h2 : i = i) : x.cast h1 h2 = x := rfl

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h1 : n = n') (h2 : i = i')
    (h3 : n' = n'') (h4 : i' = i'') : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem term {q : ℕ} (P : Collected q) {E F : Spc} (f : F ⟶ E) (h : Inv q E) (h' : Inv q F) (y : Ht q F 2 1)
    {n' i' : ℤ} (u : Ht q E n' i') (k m N : ℕ) (hN : k + m = N) (hn : n' = 2 * (k : ℤ)) (hi : i' = k)
    (h1 : n' + 2 * (m : ℤ) = 2 * (N : ℤ)) (h2 : i' + (m : ℤ) = N) :
    P.ι h' N ((cup q (pull _ f _ _ u) (cpow q y m)).cast h1 h2) =
      P.map f h' h (P.ι h k (u.cast hn hi)) * P.ι h' m (cpow q y m) := by
  subst hN hn hi
  rw [cast_rfl, P.map_ι]
  exact P.ι_mul h' k m _ _

variable {q : ℕ} {E : Spc} {N : ℕ}

def Phi (V : E ⟶ ofCat (glCat N)) (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    Ht q (PB V) (2 * (N : ℤ)) N :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ (2 * (N : ℤ)) N)

def ac (c : ∀ j : ℕ, Ht q E (2 * j) j) : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ)) :=
  fun j => (c (N - j)).cast (by have := j.isLt; omega) (by have := j.isLt; omega)

theorem phi_ι (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N))
    (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    P.ι (inv_of (PB.pr V) h) N (Phi V a) = ∑ j : Fin N, P.map (PB.pr V) (inv_of (PB.pr V) h) h
      (P.ι h (N - j) ((a j).cast (by have := j.isLt; omega) (by have := j.isLt; omega))) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (j : ℕ) := by
  unfold Phi
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [term P (PB.pr V) h (inv_of (PB.pr V) h) _ (a j) (N - j) j N (by have := j.isLt; omega)
    (by have := j.isLt; omega) (by have := j.isLt; omega), P.ι_cpow]

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2.ChernPf
variable {q : ℕ} {E : Spc} {N : ℕ}

theorem cast_inj {n i n' i' : ℤ} {x y : Ht q E n i} (h1 : n = n') (h2 : i = i') (e : x.cast h1 h2 = y.cast h1 h2) : x = y := by
  subst h1 h2; exact e

theorem cast_idx {n i : Fin N → ℤ} (a : ∀ j, Ht q E (n j) (i j)) (j j' : Fin N) (e : j = j')
    (h1 : n j = n j') (h2 : i j = i j') : (a j).cast h1 h2 = a j' := by
  subst e; rfl

theorem sum_eq (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E (2 * j) j)
    (h0 : P.ι h 0 (c 0) = 1) :
    ∑ j ∈ Finset.range (N + 1), P.map (PB.pr V) (inv_of (PB.pr V) h) h (P.ι h j (c j)) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (N - j) =
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ N + P.ι (inv_of (PB.pr V) h) N (Phi V (ac c)) := by
  have key : ∀ g : ℕ → P.R (PB V) (inv_of (PB.pr V) h),
      ∑ j ∈ Finset.range (N + 1), g j = ∑ j ∈ Finset.range N, g (N - j) + g 0 := by
    intro g
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp
  rw [key, phi_ι P h V, h0, map_one, one_mul, Nat.sub_zero, add_comm, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.sub_sub_self j.isLt.le]
  dsimp only [ac]
  rw [ChernPf.cast_cast, cast_rfl]

def mkc (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) : ∀ j : ℕ, Ht q E (2 * j) j :=
  fun j => if h0 : j = 0 then (one q E).cast (by simp [h0]) (by simp [h0])
    else if hj : j ≤ N then (a ⟨N - j, by omega⟩).cast (by simp; omega) (by simp; omega) else 0

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2
open ChernPf

theorem LeafChern_of : LeafChern := by
  intro hD1 q _ P E h N V
  have hB : Function.Bijective (Phi (q := q) V) := hD1 q V h (2 * (N : ℤ)) N
  have hι : ∀ {F : Spc} (h : Inv q F) k, Function.Injective (P.ι h k) := fun h k a b e => by
    simpa [P.π_ι] using congrArg (P.π h k) e
  have char : ∀ c, P.ι h 0 (c 0) = 1 → (IsChern P h V c ↔
      (∀ j, N < j → c j = 0) ∧ Phi V (ac c) = -cpow q (c1 q (PB.line V)) N) := by
    intro c h0
    unfold IsChern
    rw [sum_eq P h V c h0, ← P.ι_cpow, ← map_add, map_eq_zero_iff _ (hι _ _), add_eq_zero_iff_neg_eq, eq_comm]
    simp only [h0, true_and]
    exact and_congr_right fun _ => eq_comm
  have uniq : ∀ c c', IsChern P h V c → IsChern P h V c' → c = c' := by
    intro c c' hc hc'
    have hA : ac c = ac c' := hB.1 (((char c hc.1).1 hc).2.trans ((char c' hc'.1).1 hc').2.symm)
    funext j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hι h 0 (hc.1.trans hc'.1.symm)
    by_cases hjN : N < j
    · rw [hc.2.1 j hjN, hc'.2.1 j hjN]
    have := cast_inj _ _ (congrFun hA ⟨N - j, by omega⟩)
    have e : N - ((⟨N - j, by omega⟩ : Fin N) : ℕ) = j := by simp; omega
    rw [e] at this
    exact this
  obtain ⟨a, ha⟩ := hB.2 (-cpow q (c1 q (PB.line V)) N)
  have hc0 : P.ι h 0 (mkc a 0) = 1 := by
    dsimp only [mkc]
    rw [dif_pos rfl]
    exact P.ι_one h
  have hac : ac (mkc a) = a := by
    funext j
    dsimp only [ac, mkc]
    rw [dif_neg (by omega), dif_pos (by omega), ChernPf.cast_cast]
    exact cast_idx a _ _ (Fin.ext (by simp; omega)) _ _
  have hC : IsChern P h V (mkc a) := (char _ hc0).2 ⟨fun j hj => by
    dsimp only [mkc]
    rw [dif_neg (by omega), dif_neg (by omega)], by rw [hac]; exact ha⟩
  exact ⟨mkc a, hC, fun c' hc' => uniq _ _ hc' hC⟩

end LateralTheory.E.D2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCompPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def LeafCoprod : Prop := Hyps → ∀ (q : ℕ) (n i : ℤ) (m : ℕ) (Z : Fin m → Scheme.{0}),
  (∀ j, Finite (Ht q (sch.obj (Z j)) n i)) → Finite (Ht q (sch.obj (∐ Z)) n i)

def LeafCompGeom : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p],
  ∃ (m : ℕ) (Z : Fin m → Scheme.{0}) (ι : ∀ j, Z j ⟶ X), (∀ j, IsClosedImmersion (ι j) ∧ IsIntegral (Z j)) ∧
    IsProper (Sigma.desc ι) ∧ Surjective (Sigma.desc ι)

theorem LeafComp_of (hC : LeafCoprod) (hG : LeafCompGeom) : LeafComp := by
  intro hH q k _ X p _ n i hZ
  obtain ⟨m, Z, ι, hι, hP, hS⟩ := hG k p
  exact ⟨∐ Z, Sigma.desc ι, hP, hS, hC hH q n i m Z (fun j => hZ (Z j) (ι j) (hι j).1 (hι j).2)⟩

end LateralTheory.E.E4
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPointCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8

def RatModel {k : Type} [Field k] {P : Scheme.{0}} (r : P ⟶ Spec (CommRingCat.of k)) (d : ℕ) : Prop :=
  ∃ (V : P.Opens) (e : V.toScheme ⟶ 𝔸(Fin d; Spec (CommRingCat.of k))), IsOpenImmersion e ∧ Nonempty V ∧
    e ≫ (𝔸(Fin d; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) = V.ι ≫ r

def LeafPointModel : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ d : ℕ,
  ∃ (P : Scheme.{0}) (_ : IsIntegral P) (r : P ⟶ Spec (CommRingCat.of k)) (_ : IsProper r)
    (_ : SmoothOfRelativeDimension d r), RatModel r d ∧
    ∀ (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens), (W : Set P) = (Set.range y)ᶜ →
      ∃ c : Ht q (sch.obj P) (2 * d) d, pull _ (sch.map W.ι) _ _ c = 0 ∧ addOrderOf c = q

def LeafPointTransfer : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
    {P : Scheme.{0}} [IsIntegral P] (r : P ⟶ Spec (CommRingCat.of k)) [IsProper r] [SmoothOfRelativeDimension d r],
  RatModel r d →
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (_ : x ≫ p = 𝟙 _) (U : X.Opens) (_ : (U : Set X) = (Set.range x)ᶜ)
    (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens) (_ : (W : Set P) = (Set.range y)ᶜ)
    (T : Ht q (sch.obj X) (2 * d) d →+ Ht q (sch.obj P) (2 * d) d),
    ∀ c' : Ht q (sch.obj P) (2 * d) d, pull _ (sch.map W.ι) _ _ c' = 0 →
      ∃ c : Ht q (sch.obj X) (2 * d) d, pull _ (sch.map U.ι) _ _ c = 0 ∧ T c = c'

end LateralTheory.E.E8

end
end

