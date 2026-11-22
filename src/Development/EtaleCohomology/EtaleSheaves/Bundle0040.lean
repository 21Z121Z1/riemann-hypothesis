import Development.EtaleCohomology.EtaleSheaves.Bundle0016
import Development.EtaleCohomology.EtaleSheaves.Bundle0031
import Development.EtaleCohomology.EtaleSheaves.Bundle0019

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProdACFField
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.PtsPf

attribute [local instance] PrimeSpectrum.isPrime

lemma prodACF_field (K : Type) [Field K] [IsAlgClosed K] : ProdACF K := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p (by
      rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hd.ne')
    exact ⟨x, hx⟩
  · by_cases ha : a = 0
    · exact ⟨0, 1, IsIdempotentElem.zero, isUnit_one, by simp [ha]⟩
    · exact ⟨1, a, IsIdempotentElem.one, isUnit_iff_ne_zero.mpr ha, by simp⟩

lemma prodACF_pi {ι : Type} (W : ι → Type) [∀ i, CommRing (W i)] (h : ∀ i, ProdACF (W i)) :
    ProdACF (∀ i, W i) := by
  refine ⟨fun p hp hd => ?_, fun a => ?_⟩
  · have hr : ∀ i, ∃ x, (p.map (Pi.evalRingHom W i)).eval x = 0 := by
      intro i
      rcases subsingleton_or_nontrivial (W i) with hs | hs
      · exact ⟨0, Subsingleton.elim _ _⟩
      · exact (h i).1 _ (hp.map _) (by rw [hp.natDegree_map]; exact hd)
    choose x hx using hr
    refine ⟨x, funext fun i => ?_⟩
    have := Polynomial.hom_eval₂ p (RingHom.id _) (Pi.evalRingHom W i) x
    simp only [RingHom.comp_id] at this
    simp only [Polynomial.eval_map] at hx
    change (Pi.evalRingHom W i) (Polynomial.eval₂ (RingHom.id _) x p) = 0
    rw [this]
    exact hx i
  · have hr := fun i => (h i).2 (a i)
    choose e u he hu hau using hr
    refine ⟨e, u, ?_, Pi.isUnit_iff.mpr hu, funext hau⟩
    exact funext fun i => he i

abbrev WA (R : CommRingCat.{0}) : Type :=
  ∀ p : PrimeSpectrum R, AlgebraicClosure p.asIdeal.ResidueField

def phiA (R : CommRingCat.{0}) : R →+* WA R :=
  RingHom.pi fun p => (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField)

lemma surj_phiA (R : CommRingCat.{0}) : Surjective (Spec.map (CommRingCat.ofHom (phiA R))) := by
  refine ⟨fun p' => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p : PrimeSpectrum R, (p : Spec R) = p' := ⟨p', rfl⟩
  let ev : WA R →+* AlgebraicClosure p.asIdeal.ResidueField := Pi.evalRingHom _ p
  have hq : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  refine ⟨⟨RingHom.ker ev, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (phiA R) (RingHom.ker ev) = p.asIdeal
  rw [RingHom.comap_ker]
  have : ev.comp (phiA R) = (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
    (algebraMap R p.asIdeal.ResidueField) := rfl
  rw [this, RingHom.ker_comp_of_injective _ (RingHom.injective (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField))), Ideal.ker_algebraMap_residueField]

theorem Pts_of : Pts := by
  intro P _ _
  let 𝒰 := P.affineCover.finiteSubcover
  let I := 𝒰.I₀
  have hA : ∀ i : I, IsAffine (𝒰.X i) := fun i => by
    change IsAffine (P.affineCover.X _); infer_instance
  let R : I → CommRingCat.{0} := fun i => Γ(𝒰.X i, ⊤)
  let f : ∀ i, Spec (R i) ⟶ P := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  let S : I → CommRingCat.{0} := fun i => CommRingCat.of (WA (R i))
  let g : ∀ i, Spec (S i) ⟶ P := fun i => Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ f i
  refine ⟨∀ i, S i, inferInstance, inv (sigmaSpec S) ≫ Sigma.desc g, ?_, ?_⟩
  · exact prodACF_pi _ fun i => prodACF_pi _ fun p => prodACF_field _
  · have : Surjective (Sigma.desc g) := by
      apply Surjective.sigmaDesc_of_union_range_eq_univ
      have hr : ∀ i, Set.range (g i) = Set.range (𝒰.f i) := fun i => by
        have := surj_phiA (R i)
        rw [range_eq_range_of_surjective (g i) (𝒰.f i) (Spec.map (CommRingCat.ofHom (phiA (R i))) ≫ (𝒰.X i).isoSpec.inv)
          (by simp [g, f])]
      simp_rw [hr]
      exact 𝒰.iUnion_range
    infer_instance

end LateralTheory.E.PtsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProjFPf
section
noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjFPf

section Tw
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

theorem twist_apply (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

def tinv (ε : ZMod q → A) (z : ZMod q → A) : ZMod q → A := fun k => ∑ d, ε (-d) * z (k + d)

theorem twist_tinv (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : twist hε (tinv ε z) = z := by
  funext k
  rw [twist_apply]
  unfold tinv
  have : ∀ c, ε c * ∑ d, ε (-d) * z (k + c + d) = ε c * z k := by
    intro c
    rw [Finset.mul_sum, Finset.sum_eq_single (-c)]
    · rw [neg_neg, ← mul_assoc, (hε.idem c).eq, add_neg_cancel_right]
    · intro d _ hd
      have : c ≠ -d := fun h => hd (by rw [h, neg_neg])
      rw [← mul_assoc, hε.ortho this, zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul, hε.complete, one_mul]

theorem tinv_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : tinv ε (twist hε z) = z := by
  funext k
  unfold tinv
  simp_rw [twist_apply]
  have : ∀ d, ε (-d) * ∑ c, ε c * z (k + d + c) = ε (-d) * z k := by
    intro d
    rw [Finset.mul_sum, Finset.sum_eq_single (-d)]
    · rw [← mul_assoc, (hε.idem (-d)).eq, add_neg_cancel_right]
    · intro c _ hc
      rw [← mul_assoc, hε.ortho (Ne.symm hc), zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul]
  rw [show (∑ d : ZMod q, ε (-d)) = ∑ d, ε d from
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl), hε.complete, one_mul]

theorem twist_const_mul (hε : CompleteOrthogonalIdempotents ε) (a : A) (z : ZMod q → A) :
    twist hε (fun k => a * z k) = fun k => a * twist hε z k := by
  funext k
  simp only [twist_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem eq_zero_of_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (h : twist hε z = 0) : z = 0 := by
  rw [← tinv_twist hε z, h]; funext k; simp [tinv]
end Tw

section Main
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S)

theorem mem_tor {ε : ZMod q → Localization.Away (f * g)} (hε : CompleteOrthogonalIdempotents ε) (p : Amb f g q) :
    p ∈ Tor f g hε ↔ ∀ k, rL f g (p.1 k) = twist hε (fun j => rR f g (p.2 j)) k :=
  funext_iff

theorem rR_alg (a : S) : rR f g (algebraMap S (Localization.Away g) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rR; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem rL_alg (a : S) : rL f g (algebraMap S (Localization.Away f) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rL; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem unit_g : IsUnit (algebraMap S (Localization.Away (f * g)) g) := by
  refine isUnit_of_mul_isUnit_right (x := algebraMap S (Localization.Away (f * g)) f) ?_
  rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g)

theorem kill (z : Localization.Away g) (hz : rR f g z = 0) :
    ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * z = 0 := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
  dsimp only at hz ⊢
  have hb : algebraMap S (Localization.Away (f * g)) b = 0 := by
    rw [← rR_alg, ← IsLocalization.mk'_spec (Localization.Away g) b s, map_mul, hz, zero_mul]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ b).mp hb
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n)) :=
    (IsLocalization.map_units (Localization.Away g) s).mul
      (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g).pow n)
  refine (hu.mul_left_eq_zero).mp ?_
  calc algebraMap S (Localization.Away g) f ^ n * IsLocalization.mk' (Localization.Away g) b s *
        (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n))
      = algebraMap S (Localization.Away g) f ^ n *
        (IsLocalization.mk' (Localization.Away g) b s * algebraMap S (Localization.Away g) (s : S)) *
        algebraMap S (Localization.Away g) (g ^ n) := by ring
    _ = algebraMap S (Localization.Away g) ((f * g) ^ n * b) := by
        rw [IsLocalization.mk'_spec, mul_pow]; simp only [map_mul, map_pow]; ring
    _ = 0 := by simp only at hn; rw [hn, map_zero]
end Main

theorem projF : ProjF := by
  intro q _ S _ f g _ ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr1 f g hε).toAlgebra
  have hA : ∀ t : Tor f g hε, algebraMap (Tor f g hε) (ZMod q → Localization.Away f) t = (t : Amb f g q).1 :=
    fun _ => rfl
  have hf : algebraMap S (Tor f g hε) f = torMap f g hε f := rfl
  have hT1 : ((torMap f g hε f : Tor f g hε) : Amb f g q).1 = fun _ => algebraMap S (Localization.Away f) f := rfl
  have hT2 : ((torMap f g hε f : Tor f g hε) : Amb f g q).2 = fun _ => algebraMap S (Localization.Away g) f := rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [hA, hf, hT1, Pi.isUnit_iff]; intro _; exact IsLocalization.Away.algebraMap_isUnit f
  · intro s
    set w : ZMod q → Localization.Away (f * g) := tinv ε (fun k => rL f g (s k)) with hw
    obtain ⟨⟨_, n, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
    have hb' : ∀ i, ∃ a, algebraMap S (Localization.Away (f * g)) a = (f * g) ^ n • w i :=
      fun i => RingHom.mem_rangeS.mp (hb i)
    choose a ha using hb'
    let y : ZMod q → Localization.Away g := fun k =>
      IsLocalization.mk' (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    have hy : ∀ k, rR f g (y k) = algebraMap S _ (f ^ n) * w k := by
      intro k
      have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (g ^ n)) := by
        rw [map_pow]; exact (unit_g f g).pow n
      apply hu.mul_left_injective
      have e1 := IsLocalization.mk'_spec (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
      simp only at e1 ⊢
      rw [← rR_alg f g (g ^ n), ← map_mul, e1]
      simp only [rR_alg, ha k, Algebra.smul_def, mul_pow, map_mul, map_pow]
      ring
    let x : ZMod q → Localization.Away f := fun k => s k * algebraMap S _ f ^ n
    have hmem : ((x, y) : Amb f g q) ∈ Tor f g hε := by
      rw [mem_tor]; intro k
      have h2 : (fun j => rR f g (((x, y) : Amb f g q).2 j)) = fun j => algebraMap S _ (f ^ n) * w j := funext hy
      rw [h2, twist_const_mul, hw, twist_tinv]
      show rL f g (s k * algebraMap S _ f ^ n) = _
      rw [map_mul, map_pow, rL_alg, map_pow]; ring
    refine ⟨n, ⟨(x, y), hmem⟩, ?_⟩
    show s * (((torMap f g hε f : Tor f g hε) : Amb f g q).1) ^ n = x
    rw [hT1]
    funext k
    simp only [Pi.mul_apply, Pi.pow_apply]
    rfl
  · intro a b hab
    have hc1 : ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by
      rw [← hA (a - b), map_sub, hab, sub_self]
    have hm := (mem_tor f g hε _).mp (a - b).2
    have htw : twist hε (fun j => rR f g (((a - b : Tor f g hε) : Amb f g q).2 j)) = 0 := by
      funext k; rw [← hm k, hc1]; simp
    have hc2 := eq_zero_of_twist hε _ htw
    have hk : ∀ k, ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * ((a - b : Tor f g hε) : Amb f g q).2 k = 0 :=
      fun k => kill f g _ (congrFun hc2 k)
    choose m hm' using hk
    refine ⟨Finset.univ.sup m, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    apply Subtype.ext
    apply Prod.ext
    · have e : ((algebraMap S (Tor f g hε) f ^ Finset.univ.sup m : Tor f g hε) : Amb f g q).1 *
          ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by rw [hc1, mul_zero]
      exact e
    · funext k
      show (algebraMap S (Localization.Away g) f) ^ (Finset.univ.sup m) * ((a - b : Tor f g hε) : Amb f g q).2 k = 0
      rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : m k ≤ Finset.univ.sup m), pow_add, mul_assoc, hm' k,
        mul_zero]

end LateralTheory.E.ProjFPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProjGPf
section
noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjGPf

variable {S : Type} [CommRing S]

theorem isUnit_f_fg (f g : S) : IsUnit (algebraMap S (Localization.Away (f * g)) f) :=
  isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f g)) (IsLocalization.Away.algebraMap_isUnit (f * g))

theorem rL_alg (f g : S) (a : S) :
    rL f g (algebraMap S _ a) = algebraMap S (Localization.Away (f * g)) a :=
  IsLocalization.Away.awayToAwayRight_eq f g a

theorem rR_alg (f g : S) (a : S) :
    rR f g (algebraMap S _ a) = algebraMap S (Localization.Away (f * g)) a :=
  IsLocalization.Away.awayToAwayLeft_eq g f a

theorem rL_surj {ι : Type} [Finite ι] (f g : S) (w : ι → Localization.Away (f * g)) :
    ∃ (n : ℕ) (x : ι → Localization.Away f), ∀ k, rL f g (x k) = algebraMap S _ (g ^ n) * w k := by
  obtain ⟨⟨b, hb'⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hb'
  choose a ha using hb
  refine ⟨n, fun k => IsLocalization.mk' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f), fun k => ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (f ^ n)) := by
    rw [map_pow]; exact (isUnit_f_fg f g).pow n
  apply hu.mul_left_cancel
  have hs := IsLocalization.mk'_spec' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  change algebraMap S _ (f ^ n) * _ = _ at hs
  rw [← rL_alg, ← map_mul, hs, rL_alg, ha k, Algebra.smul_def]
  change algebraMap S _ ((f * g) ^ n) * w k = _
  rw [mul_pow, map_mul, mul_assoc, rL_alg]

theorem rL_ker (f g : S) (x : Localization.Away f) (hx : rL f g x = 0) :
    ∃ n : ℕ, algebraMap S _ (g ^ n) * x = 0 := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have h0 : algebraMap S (Localization.Away (f * g)) a = 0 := by
    rw [← rL_alg, ← hs, map_mul, hx, zero_mul]
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ a).mp h0
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away f) (f ^ n * s)) :=
    IsLocalization.map_units (Localization.Away f)
      (⟨f ^ n * s, Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers f) n) s.2⟩ : Submonoid.powers f)
  apply (hu.mul_left_eq_zero).mp
  have e1 : algebraMap S (Localization.Away f) (g ^ n) * x * algebraMap S _ (f ^ n * s)
      = algebraMap S _ (g ^ n * f ^ n) * (x * algebraMap S _ (s : S)) := by
    simp only [map_mul]; ring
  rw [e1, hs, ← map_mul, show g ^ n * f ^ n * a = (f * g) ^ n * a by ring, hm, map_zero]

theorem rL_ker_fam {ι : Type} [Fintype ι] (f g : S) (x : ι → Localization.Away f)
    (hx : ∀ k, rL f g (x k) = 0) : ∃ n : ℕ, ∀ k, algebraMap S _ (g ^ n) * x k = 0 := by
  choose n hn using fun k => rL_ker f g (x k) (hx k)
  refine ⟨Finset.univ.sup n, fun k => ?_⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : n k ≤ _), pow_add, map_mul, mul_assoc, hn k,
    mul_zero]

theorem twist_apply {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}
    (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

theorem ProjG_of : ProjG := by
  intro q _ S _ f g hfg ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr2 f g hε).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have e : algebraMap (Tor f g hε) (ZMod q → Localization.Away g) (algebraMap S (Tor f g hε) g ^ n)
        = fun _ => algebraMap S (Localization.Away g) g ^ n := by
      rw [map_pow]; rfl
    rw [e]
    exact Pi.isUnit_iff.mpr fun _ => (IsLocalization.Away.algebraMap_isUnit g).pow n
  · intro y
    obtain ⟨n, x, hx⟩ := rL_surj f g (twist hε (fun k => rR f g (y k)))
    have hmem : ((x, fun k => algebraMap S _ (g ^ n) * y k) : Amb f g q) ∈ Tor f g hε := by
      show h1 f g _ = h2 f g hε _
      funext k
      change rL f g (x k) = ∑ c, ε c * rR f g (algebraMap S _ (g ^ n) * y (k + c))
      rw [hx k, twist_apply]
      simp only [map_mul, rR_alg]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    refine ⟨(⟨_, hmem⟩, ⟨algebraMap S _ g ^ n, n, rfl⟩), ?_⟩
    show y * pr2 f g hε (torMap f g hε g ^ n) = pr2 f g hε ⟨_, hmem⟩
    rw [map_pow]
    funext k
    change y k * (algebraMap S (Localization.Away g) g) ^ n = algebraMap S _ (g ^ n) * y k
    rw [map_pow, mul_comm]
  · intro t1 t2 h
    have h0 : (t1 - t2).1.2 = 0 := by
      have : pr2 f g hε (t1 - t2) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr h
      exact this
    have hx : ∀ k, rL f g ((t1 - t2).1.1 k) = 0 := by
      intro k
      have hm : h1 f g (t1 - t2).1 = h2 f g hε (t1 - t2).1 := (t1 - t2).2
      have hk := congrFun hm k
      change rL f g ((t1 - t2).1.1 k) = ∑ c, ε c * rR f g ((t1 - t2).1.2 (k + c)) at hk
      rw [hk, h0]; simp
    obtain ⟨n, hn⟩ := rL_ker_fam f g (fun k => (t1 - t2).1.1 k) hx
    refine ⟨⟨algebraMap S _ g ^ n, n, rfl⟩, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    show torMap f g hε g ^ n * (t1 - t2) = 0
    apply Subtype.ext
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · change (algebraMap S (Localization.Away f) g) ^ n * (t1 - t2).1.1 k = 0
      rw [← map_pow]; exact hn k
    · change (algebraMap S (Localization.Away g) g) ^ n * (t1 - t2).1.2 k = 0
      rw [h0]; simp

end LateralTheory.E.ProjGPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RootPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.RootPf

lemma unit_sec {Z : Scheme.{0}} (q : ℕ) (A : Type) [CommRing A] (p : Z ⟶ Spec (CommRingCat.of A))
    (hq : IsUnit (q : A)) (U : Z.Opens) : IsUnit (q : Γ(Z, U)) := by
  let f : CommRingCat.of A ⟶ Γ(Z, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
  have := hq.map f.hom
  simpa using this

lemma prim_of_aic (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] (hT : AIC T)
    (hq : IsUnit (q : T)) : ∃ a : T, IsPrimitiveRoot a q := by
  have : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨a, ha⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  exact ⟨a, (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := a)).1 ha⟩

lemma local_root {Z : Scheme.{0}} [IsIntegral Z]
    (hZ : ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U))
    (q : ℕ) [NeZero q] (hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U))) (ζ : Z.functionField)
    (hζ : IsPrimitiveRoot ζ q) (V : Z.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ s : Γ(Z, V), (Z.germToFunctionField V).hom s = ζ := by
  obtain ⟨a, ha⟩ := prim_of_aic q Γ(Z, V)
    (hZ V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)) (hqU V)
  have hb := ha.map_of_injective (f := (Z.germToFunctionField V).hom) (Z.germToFunctionField_injective V)
  obtain ⟨i, -, hi⟩ := hb.eq_pow_of_pow_eq_one hζ.pow_eq_one
  exact ⟨a ^ i, by rw [map_pow]; exact hi⟩

theorem Root_of : LateralTheory.E.ChartSurjCut.Root := by
  intro q A _ Z p hZ hq
  obtain ⟨hI, hA⟩ := hZ
  have hqU : ∀ U : Z.Opens, IsUnit (q : Γ(Z, U)) := fun U => unit_sec q A p hq U
  obtain ⟨x⟩ := (inferInstance : Nonempty Z)
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨x, trivial⟩⟩
  have hq0 : NeZero q := ⟨by rintro rfl; exact not_isUnit_zero (M₀ := Γ(Z, ⊤)) (by simpa using hqU ⊤)⟩
  have hbasis : ∀ {U : Z.Opens} {y : Z}, y ∈ U → ∃ U' ∈ Z.affineOpens, y ∈ U' ∧ U' ≤ U :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
  have haff : ∀ y : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ y ∈ U := by
    intro y
    obtain ⟨U, hU, hy, -⟩ := hbasis (show y ∈ (⊤ : Z.Opens) from trivial)
    exact ⟨U, hU, hy⟩
  obtain ⟨U₀, hU₀, hx⟩ := haff x
  have : Nonempty U₀ := ⟨⟨x, hx⟩⟩
  obtain ⟨a₀, ha₀⟩ := prim_of_aic q Γ(Z, U₀) (hA U₀ hU₀ ⟨x, hx⟩) (hqU U₀)
  set ζ : Z.functionField := (Z.germToFunctionField U₀).hom a₀ with hζdef
  have hζ : IsPrimitiveRoot ζ q :=
    ha₀.map_of_injective (f := (Z.germToFunctionField U₀).hom) (Z.germToFunctionField_injective U₀)
  let ι := {V : Z.Opens // IsAffineOpen V ∧ Nonempty V}
  let U : ι → Z.Opens := fun i => i.1
  have instU : ∀ i : ι, Nonempty (U i) := fun i => i.2.2
  have hex : ∀ i : ι, ∃ s : Γ(Z, U i), (Z.germToFunctionField (U i)).hom s = ζ := fun i =>
    @local_root Z hI hA q hq0 hqU ζ hζ i.1 i.2.1 i.2.2
  let sf : ∀ i : ι, Γ(Z, U i) := fun i => Classical.choose (hex i)
  have hsf : ∀ i : ι, (Z.germToFunctionField (U i)).hom (sf i) = ζ := fun i => Classical.choose_spec (hex i)
  have hcov : (⊤ : Z.Opens) ≤ iSup U := by
    intro y _
    obtain ⟨V, hV, hy⟩ := haff y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨⟨y, hy⟩⟩⟩, hy⟩
  have hcomp : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have : Nonempty (U i ⊓ U j : Z.Opens) := by
      obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (U i).isOpen (U j).isOpen
        (by obtain ⟨⟨y, hy⟩⟩ := i.2.2; exact ⟨y, hy⟩) (by obtain ⟨⟨y, hy⟩⟩ := j.2.2; exact ⟨y, hy⟩)
      exact ⟨⟨y, hy⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf i)) = Z.presheaf.germ _ _ _ (Z.presheaf.map _ (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact (hsf i).trans (hsf j).symm
  obtain ⟨s0, hs, -⟩ := Z.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov sf hcomp
  let s : Γ(Z, ⊤) := s0
  change ∀ i : ι, Z.presheaf.map (homOfLE le_top).op s = sf i at hs
  have hgs : (Z.germToFunctionField ⊤).hom s = ζ := by
    have h1 := hs ⟨U₀, hU₀, inferInstance⟩
    have h2 := hsf ⟨U₀, hU₀, inferInstance⟩
    rw [← h1] at h2
    change Z.presheaf.germ _ _ _ (Z.presheaf.map _ s) = ζ at h2
    rw [TopCat.Presheaf.germ_res_apply] at h2
    exact h2
  have hps : IsPrimitiveRoot s q := by
    have h' : IsPrimitiveRoot ((Z.germToFunctionField ⊤).hom s) q := by rw [hgs]; exact hζ
    exact IsPrimitiveRoot.of_map_of_injective h' (Z.germToFunctionField_injective ⊤)
  have : NeZero (q : Γ(Z, ⊤)) := ⟨(hqU ⊤).ne_zero⟩
  refine ⟨⟨s, hqU ⊤, ?_⟩⟩
  have hr := (Polynomial.isRoot_cyclotomic_iff (n := q) (μ := s)).2 hps
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hr

end LateralTheory.E.RootPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TruncationPieces
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf

namespace LateralTheory.E.TruncationPieces

def RelK (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (HK.pull R f F m)) ∧ Function.Injective (HK.pull R f F n)

def piece (R : Type) [CommRing R] {U E : Spc} (u : U ⟶ E) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj U).X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj E).X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map u).f (-(p : ℤ)))

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (p : ℕ) (k : ℤ),
  RelZS R F k (disc.map (u.app (Opposite.op (SimplexCategory.mk p)))) → RelK R F (k + p) (piece R u p)

def Filt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ p : ℕ, RelK R F n (piece R u p)) → RelZS R F n u

theorem etale_relK_single_degree_pieces_of_piece_and_filtration (hP : Piece) (hF : Filt) : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := by
  intro R _ F U E u n hlow h0
  refine hF R F u n (fun p => ?_)
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have := hP R F u 0 n h0
    simpa using this
  · have hk : n - (p : ℤ) < n := by omega
    have := hP R F u p (n - p) (hlow p (n - p) hk)
    simpa using this

end LateralTheory.E.TruncationPieces
end
end

