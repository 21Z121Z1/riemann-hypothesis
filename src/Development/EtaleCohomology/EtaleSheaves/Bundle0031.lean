import Development.EtaleCohomology.EtaleSheaves.Bundle0009
import Development.EtaleCohomology.EtaleSheaves.Bundle0014
import Development.EtaleCohomology.EtaleSheaves.Bundle0013

-- bundled from Development.EtaleCohomology.EtaleSheaves.TorEtPf
section
noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf

namespace LateralTheory.E.TorEtPf

def LocalGlue : Prop := ∀ (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Fintype ι] [Nonempty ι] (f g : S),
  Ideal.span {f, g} = ⊤ →
  Nonempty (Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) →
  Nonempty (Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) →
  Algebra.Etale S C ∧ Module.Finite S C ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap S C))

def LocF : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Nonempty (Localization.Away (algebraMap S (Tor f g hε) f) ≃ₐ[S] (ZMod q → Localization.Away f))

def LocG : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Nonempty (Localization.Away (algebraMap S (Tor f g hε) g) ≃ₐ[S] (ZMod q → Localization.Away g))

theorem surj_local (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Nonempty ι] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) (p : PrimeSpectrum S) (hp : f ∉ p.asIdeal) :
    ∃ Q : PrimeSpectrum C, PrimeSpectrum.comap (algebraMap S C) Q = p := by
  have hr : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact hp
  obtain ⟨P, hP⟩ := hr
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨PrimeSpectrum.comap (algebraMap C (Localization.Away (algebraMap S C f)))
    (PrimeSpectrum.comap (e : Localization.Away (algebraMap S C f) →+* (ι → Localization.Away f))
      (PrimeSpectrum.comap (Pi.evalRingHom _ i) P)), ?_⟩
  rw [← hP]
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have : (e (algebraMap C (Localization.Away (algebraMap S C f)) (algebraMap S C x))) i = algebraMap S (Localization.Away f) x := by
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]; rfl
  simp only [RingHom.coe_coe, Pi.evalRingHom_apply, this]

theorem TorEt_of (hL : LocalGlue) (hF : LocF) (hG : LocG) : TorEt := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  exact hL S (Tor f g hε) (ZMod q) f g hfg (hF q S f g hfg ε hε) (hG q S f g hfg ε hε)

theorem surj_glue (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Nonempty ι] (f g : S) (hfg : Ideal.span {f, g} = ⊤)
    (ef : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f))
    (eg : Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) := by
  intro p
  by_cases hf : f ∈ p.asIdeal
  · have hg : g ∉ p.asIdeal := by
      intro hg
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hfg, Ideal.span_le]
      rintro x (rfl | rfl) <;> assumption
    exact surj_local S C ι g eg p hg
  · exact surj_local S C ι f ef p hf

def LocalEF : Prop := ∀ (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Fintype ι] [Nonempty ι] (f g : S),
  Ideal.span {f, g} = ⊤ →
  Nonempty (Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) →
  Nonempty (Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) →
  Algebra.Etale S C ∧ Module.Finite S C

theorem localGlue_of (h : LocalEF) : LocalGlue := by
  intro S C ι _ _ _ _ _ f g hfg ⟨ef⟩ ⟨eg⟩
  obtain ⟨h1, h2⟩ := h S C ι f g hfg ⟨ef⟩ ⟨eg⟩
  exact ⟨h1, h2, surj_glue S C ι f g hfg ef eg⟩

theorem TorEt_of' (hE : LocalEF) (hF : LocF) (hG : LocG) : TorEt := TorEt_of (localGlue_of hE) hF hG

theorem awayMap_eq (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) :
    Localization.awayMap (algebraMap S C) f =
      (e.symm : (ι → Localization.Away f) →+* Localization.Away (algebraMap S C f)).comp
        (algebraMap (Localization.Away f) (ι → Localization.Away f)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext s
  simp only [RingHom.comp_apply]
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have h1 : algebraMap (Localization.Away f) (ι → Localization.Away f) (algebraMap S (Localization.Away f) s)
      = algebraMap S (ι → Localization.Away f) s := rfl
  rw [h1, RingHom.coe_coe, AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply S C (Localization.Away (algebraMap S C f)) s)

theorem away_prop (P : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop) (hP : RingHom.RespectsIso @P)
    (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f))
    (hb : P (algebraMap (Localization.Away f) (ι → Localization.Away f))) :
    P (Localization.awayMap (algebraMap S C) f) := by
  rw [awayMap_eq S C ι f e]
  exact hP.1 _ e.symm.toRingEquiv hb

theorem localEF_of : LocalEF := by
  intro S C ι _ _ _ _ _ f g hfg ⟨ef⟩ ⟨eg⟩
  have key : ∀ (P : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop), RingHom.RespectsIso @P →
      RingHom.OfLocalizationSpan @P →
      (∀ h : S, P (algebraMap (Localization.Away h) (ι → Localization.Away h))) → P (algebraMap S C) := by
    intro P hP hL hb
    apply hL (algebraMap S C) {f, g} hfg
    rintro ⟨r, hr⟩
    rcases hr with rfl | rfl
    · exact away_prop P hP S C ι _ ef (hb _)
    · exact away_prop P hP S C ι _ eg (hb _)
  refine ⟨?_, ?_⟩
  · rw [← RingHom.etale_algebraMap]
    exact key _ RingHom.Etale.respectsIso RingHom.Etale.ofLocalizationSpan
      (fun h => RingHom.etale_algebraMap.mpr inferInstance)
  · rw [← RingHom.finite_algebraMap]
    exact key _ RingHom.finite_respectsIso RingHom.finite_ofLocalizationSpan
      (fun h => RingHom.finite_algebraMap.mpr inferInstance)

theorem TorEt_of'' (hF : LocF) (hG : LocG) : TorEt := TorEt_of' localEF_of hF hG

def pr1 {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}
    (hε : CompleteOrthogonalIdempotents ε) : Tor f g hε →+* (ZMod q → Localization.Away f) :=
  (RingHom.fst _ _).comp (Tor f g hε).subtype

def ProjF : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  letI := (pr1 f g hε).toAlgebra
  IsLocalization.Away (algebraMap S (Tor f g hε) f) (ZMod q → Localization.Away f)

theorem locF_of (h : ProjF) : LocF := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  letI := (pr1 f g hε).toAlgebra
  haveI := h q S f g hfg ε hε
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Tor f g hε) f))
    (Localization.Away (algebraMap S (Tor f g hε) f)) (ZMod q → Localization.Away f)
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => ?_)⟩
  have h1 : algebraMap S (Localization.Away (algebraMap S (Tor f g hε) f)) s =
      algebraMap (Tor f g hε) (Localization.Away (algebraMap S (Tor f g hε) f)) (torMap f g hε s) := rfl
  rw [AlgEquiv.coe_ringEquiv, h1, AlgEquiv.commutes]
  rfl

def pr2 {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}
    (hε : CompleteOrthogonalIdempotents ε) : Tor f g hε →+* (ZMod q → Localization.Away g) :=
  (RingHom.snd _ _).comp (Tor f g hε).subtype

def ProjG : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  letI := (pr2 f g hε).toAlgebra
  IsLocalization.Away (algebraMap S (Tor f g hε) g) (ZMod q → Localization.Away g)

theorem locG_of (h : ProjG) : LocG := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  letI := (pr2 f g hε).toAlgebra
  haveI := h q S f g hfg ε hε
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Tor f g hε) g))
    (Localization.Away (algebraMap S (Tor f g hε) g)) (ZMod q → Localization.Away g)
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => ?_)⟩
  have h1 : algebraMap S (Localization.Away (algebraMap S (Tor f g hε) g)) s =
      algebraMap (Tor f g hε) (Localization.Away (algebraMap S (Tor f g hε) g)) (torMap f g hε s) := rfl
  rw [AlgEquiv.coe_ringEquiv, h1, AlgEquiv.commutes]
  rfl

theorem TorEt_of_proj (hF : ProjF) (hG : ProjG) : TorEt := TorEt_of'' (locF_of hF) (locG_of hG)

end LateralTheory.E.TorEtPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TwFBijPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.TwFBijPf

theorem aeval_res {C : Type} [CommRing C] [IsLocalRing C] (q : ℕ) (x : C) :
    aeval (residue C x) (cyclotomic q ℤ) = residue C (aeval x (cyclotomic q ℤ)) :=
  by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂]; congr 1

theorem isRoot_iff {K : Type} [CommRing K] (q : ℕ) (x : K) :
    IsRoot (cyclotomic q K) x ↔ aeval x (cyclotomic q ℤ) = 0 := by
  rw [← map_cyclotomic_int, IsRoot, Polynomial.eval_map, aeval_def, algebraMap_int_eq]

theorem res_prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot (residue C ζ) q := by
  haveI : NeZero ((q : ℕ) : ResidueField C) := ⟨by
    have := hq.map (residue C); rw [map_natCast] at this; exact this.ne_zero⟩
  rw [← isRoot_cyclotomic_iff, isRoot_iff]
  exact (aeval_res q ζ).trans (by rw [h, map_zero])

theorem pow_q {C : Type} [CommRing C] {q : ℕ} {ζ : C} (h : aeval ζ (cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ζ) hg
  simp [h] at this
  exact sub_eq_zero.1 this

theorem prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot ζ q := by
  refine ⟨pow_q h, fun l hl => (res_prim hq h).dvd_of_pow_eq_one l ?_⟩
  rw [← map_pow, hl, map_one]

theorem uniq {C : Type} [CommRing C] [IsLocalRing C] {n : ℕ} (hn : IsUnit (n : C)) {x y : C} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hr : residue C x = residue C y) : x = y := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have key := (Commute.all x y).geom_sum₂_mul n
  rw [hx, hy, sub_self] at key
  have hS : IsUnit (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) := by
    rw [← residue_ne_zero_iff_isUnit, map_sum]
    have : ∀ i ∈ Finset.range n, residue C (x ^ i * y ^ (n - 1 - i)) = residue C x ^ (n - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, ← hr, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : IsUnit (residue C (n : C)) := hn.map _
    have h2 : IsUnit (residue C x) := (show IsUnit x from ⟨⟨x, x ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx],
      by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx]⟩, rfl⟩).map _
    rw [map_natCast] at h1
    exact (h1.mul (h2.pow _)).ne_zero
  have := hS.mul_right_eq_zero.1 key
  exact sub_eq_zero.1 this

theorem pow_rep {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {η ξ : C}
    (hη : aeval η (cyclotomic q ℤ) = 0) (hξ : aeval ξ (cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = η ^ (a : ZMod q).val := by
  obtain ⟨i, hi, he⟩ := (res_prim hq hη).eq_pow_of_pow_eq_one (ξ := residue C ξ) (by rw [← map_pow, pow_q hξ, map_one])
  have hηi : η ^ i = ξ := uniq hq (by rw [← pow_mul, mul_comm, pow_mul, pow_q hη, one_pow]) (pow_q hξ) (by rw [map_pow, he])
  have hc : i.Coprime q := ((prim hq hη).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hηi ▸ prim hq hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hηi]

theorem pow_inj {C : Type} [CommRing C] {q : ℕ} [NeZero q] {η : C} (hη : IsPrimitiveRoot η q) {a b : (ZMod q)ˣ}
    (h : η ^ (a : ZMod q).val = η ^ (b : ZMod q).val) : a = b :=
  Units.ext (ZMod.val_injective q (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_root {A : Type} [CommRing A] {q : ℕ} [NeZero q] (hq : IsUnit (q : A)) (hA : SH A) :
    ∃ ζ : A, aeval ζ (cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hS⟩ := hA
  haveI : NeZero ((q : ℕ) : ResidueField A) := ⟨by
    have := hq.map (residue A); rw [map_natCast] at this; exact this.ne_zero⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField A))
    (ne_of_gt (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q)))) (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective x
  have hd : IsUnit ((cyclotomic q A).derivative.eval a0) := by
    rw [← residue_ne_zero_iff_isUnit]
    have := (separable_cyclotomic q (ResidueField A)).aeval_derivative_ne_zero (x := residue A a0) (by
      rw [aeval_def, Algebra.algebraMap_self, eval₂_id]; exact hx)
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← map_cyclotomic q (residue A), derivative_map,
      Polynomial.eval_map, Polynomial.eval₂_hom] at this
    exact this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q A) (cyclotomic.monic q A) a0 (by
    rw [← residue_eq_zero_iff, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]; exact hx) hd
  exact ⟨a, (isRoot_iff q a).1 ha⟩

section Gen
variable {q : ℕ} [NeZero q] (i : ℤ) {C : Type} [CommRing C] [IsLocalRing C]

theorem pmod {η : C} (hη : IsPrimitiveRoot η q) (n : ℕ) : η ^ (n % q) = η ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]

def ex (η ξ : Prim q C) : (ZMod q)ˣ := Classical.choose (pow_rep η.2.1 η.2.2 ξ.2.2)

theorem ex_spec (η ξ : Prim q C) : ξ.1 = η.1 ^ (ex η ξ : ZMod q).val := Classical.choose_spec (pow_rep η.2.1 η.2.2 ξ.2.2)

theorem ex_pow (η ξ ζ : Prim q C) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ex η ξ = ex η ζ * a := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, h, ex_spec η ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, pmod hη]

theorem ex_self (η : Prim q C) : ex η η = 1 := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, Units.val_one, ZMod.val_one_eq_one_mod, pmod hη, pow_one]

def psi (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ => ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)))

theorem rel_le (η : Prim q C) : twRel q i C ≤ LinearMap.ker (psi i η) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, psi, Finsupp.linearCombination_single, ex_pow η ξ ζ a h,
    mul_zpow, Units.val_mul]
  apply ULift.ext
  simp [mul_comm]

def Psi (η : Prim q C) : ((Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  (twRel q i C).liftQ (psi i η) (rel_le i η)

def gen (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C := Submodule.Quotient.mk (Finsupp.single η 1)

theorem Psi_gen (η : Prim q C) : Psi i η (gen i η) = 1 := by
  simp [Psi, gen, psi, Finsupp.linearCombination_single, ex_self]
  rfl

theorem decomp (η : Prim q C) (z : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) : z = Psi i η z • gen i η := by
  induction z using Submodule.Quotient.induction_on with
  | H x =>
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Submodule.Quotient.mk_add, map_add, add_smul, ← hx, ← hy]
  | single ξ c =>
    have hrel : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single η (ULift.up (((ex η η * ex η ξ) ^ i : (ZMod q)ˣ) : ZMod q))
        ∈ twRel q i C := by
      refine Submodule.subset_span ⟨η, ξ, ex η ξ, ex_spec η ξ, ?_⟩
      rw [ex_self, one_mul]
    rw [ex_self, one_mul] at hrel
    have h1 : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) =
        ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)) • gen i η := by
      rw [gen, ← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      exact (Submodule.Quotient.eq _).2 hrel
    have h2 : (Finsupp.single ξ c : Prim q C →₀ ULift.{1} (ZMod q)) = c • Finsupp.single ξ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h2, Submodule.Quotient.mk_smul, h1, smul_smul]
    congr 1
    rw [map_smul, Psi_gen, smul_eq_mul, mul_one]

end Gen

theorem bij_ty {q : ℕ} [NeZero q] (i : ℤ) {X Y : Type} [CommRing X] [CommRing Y] [IsLocalRing X] [IsLocalRing Y]
    (g : X →+* Y) (ζ : Prim q X) :
    Function.Bijective (Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)) := by
  set F := Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)
  have hF : ∀ z, F z = Psi i ζ z • gen i (Prim.map g ζ) := by
    intro z
    conv_lhs => rw [decomp i ζ z]
    rw [map_smul]
    congr 1
    simp only [F, gen, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have hP : ∀ z, Psi i (Prim.map g ζ) (F z) = Psi i ζ z := by
    intro z
    rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
  refine ⟨fun z1 z2 h => ?_, fun w => ⟨Psi i (Prim.map g ζ) w • gen i ζ, ?_⟩⟩
  · rw [decomp i ζ z1, decomp i ζ z2, ← hP z1, ← hP z2, h]
  · rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
    exact (decomp i _ w).symm

theorem bij_gen {q : ℕ} [NeZero q] (i : ℤ) {X Y : CommRingCat.{0}} [IsLocalRing X] [IsLocalRing Y] (g : X ⟶ Y)
    (ζ : Prim q X) : Function.Bijective ((twF q i).map g).hom :=
  bij_ty i g.hom ζ

theorem TwFBij_of : LateralTheory.E.SHEqvPf.TwFBij := by
  intro q _ i A B f hq hA hB
  obtain ⟨hHA, hSA⟩ := hA
  obtain ⟨hHB, -⟩ := hB
  have hloc : ∀ (R : CommRingCat.{0}), IsLocalRing R → IsLocalRing Γ(Spec R, ⊤) := by
    intro R _
    let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    haveI : Nontrivial Γ(Spec R, ⊤) := e.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  haveI := hloc A inferInstance
  haveI := hloc B inferInstance
  obtain ⟨ζ, hζ⟩ := exists_root hq ⟨hHA, hSA⟩
  exact bij_gen i _ (Prim.map (Scheme.ΓSpecIso A).inv.hom ⟨ζ, hq, hζ⟩)

end LateralTheory.E.TwFBijPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ZCovPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

namespace LateralTheory.E.ZCovPf
set_option linter.style.haveILetI false

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hc : (e : R →+* S).comp e.symm.toRingHom = RingHom.id S := by ext x; simp
  have hq : p = (p.map e.symm.toRingHom).map (e : R →+* S) := by
    rw [Polynomial.map_map, hc, Polynomial.map_id]
  rw [hq, show e a = (e : R →+* S) a from rfl, Polynomial.eval_map_apply, ha, map_zero]

theorem good_of_affine {A : Type} [CommRing A] {Z W : Scheme.{0}} (hZ : AICSch Z) (j : W ⟶ Z) [IsOpenImmersion j]
    [IsAffine W] (p : Z ⟶ Spec (CommRingCat.of A)) : Good (j ≫ p) := by
  by_cases hW : IsEmpty W
  · exact Or.inl hW
  right
  obtain ⟨x⟩ : Nonempty W := not_isEmpty_iff.mp hW
  have hO : IsAffineOpen (j ''ᵁ ⊤) := (isAffineOpen_top W).image_of_isOpenImmersion j
  have hne : ((j ''ᵁ ⊤ : Z.Opens) : Set Z).Nonempty := ⟨j x, x, trivial, rfl⟩
  have hA : AIC Γ(W, ⊤) := aic_of_equiv (j.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ hO hne)
  haveI : IsIntegral Z := hZ.1
  haveI : Nonempty W := ⟨x⟩
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion j
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨x, trivial⟩⟩
  let φ : A →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop).hom
  letI : Algebra A Γ(W, ⊤) := φ.toAlgebra
  refine ⟨Γ(W, ⊤), inferInstance, inferInstance, inferInstance, hA, W.isoSpec, ?_⟩
  have hφ : CommRingCat.ofHom (algebraMap A Γ(W, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop := rfl
  rw [hφ, Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

attribute [local instance] MvPolynomial.gradedAlgebra

def D (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

theorem D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X ℤ i)) (hm := Nat.one_pos)

theorem D_inf : IsAffineOpen (D 0 ⊓ D 1) := by
  have h := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (MvPolynomial.X 0 * MvPolynomial.X 1) (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((MvPolynomial.isHomogeneous_X ℤ 0).mul (MvPolynomial.isHomogeneous_X ℤ 1))) (hm := Nat.two_pos)
  rw [Proj.basicOpen_mul] at h
  exact h

theorem D_cover : D 0 ⊔ D 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ)) ?_
  · refine eq_top_iff.mpr (le_trans (le_of_eq h.symm) (iSup_le fun i => ?_))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · intro x hx
    have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx
    have hc : MvPolynomial.coeff 0 x = 0 := by
      rw [GradedRing.proj_apply] at h0
      have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) x) 0 : MvPolynomial (Fin 2) ℤ) =
          MvPolynomial.homogeneousComponent 0 x := MvPolynomial.decomposition.decompose'_apply x 0
      rw [e] at h0
      have := congrArg (MvPolynomial.coeff 0) h0
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero] at this
      simpa using this
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hne
    push Not at hne
    have hm0 : m = 0 := Finsupp.ext fun i => hne i trivial
    subst hm0
    exact (MvPolynomial.mem_support_iff.mp hm) hc

theorem projectiveLine_integers_affine_cover_absolutely_integrally_closed : ZCov := by
  intro A _ Z p hp hZ
  obtain ⟨L, u, l, hu, ⟨-, f0, hpb⟩, rfl⟩ := hp
  have hf0 : IsAffineHom f0 :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  let φ : Z ⟶ P1 := u ≫ f0
  let U : Z.Opens := φ ⁻¹ᵁ D 0
  let V : Z.Opens := φ ⁻¹ᵁ D 1
  have hU : IsAffineOpen U := (D_affine 0).preimage φ
  have hV : IsAffineOpen V := (D_affine 1).preimage φ
  have hUV : IsAffineOpen (U ⊓ V) := D_inf.preimage φ
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  haveI : IsAffine (U ⊓ V : Z.Opens) := hUV
  haveI : IsAffine (pullback U.ι V.ι) := IsAffine.of_isIso (isPullback_opens_inf U V).isoPullback.inv
  refine ⟨U, V, U.ι, V.ι, inferInstance, inferInstance, ?_, good_of_affine hZ U.ι _, good_of_affine hZ V.ι _, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have h := congrArg (fun O : P1.Opens => ((φ ⁻¹ᵁ O : Z.Opens) : Set Z)) D_cover
    simpa [U, V] using h
  · rw [← Category.assoc]
    exact good_of_affine hZ (pullback.fst U.ι V.ι ≫ U.ι) _

end LateralTheory.E.ZCovPf
end
end

