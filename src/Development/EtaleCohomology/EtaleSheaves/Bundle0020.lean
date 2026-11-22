import Development.EtaleCohomology.EtaleSheaves.Bundle0013
import Development.EtaleCohomology.EtaleSheaves.Bundle0012
import Development.EtaleCohomology.EtaleSheaves.Bundle0007
import Development.EtaleCohomology.EtaleSheaves.Bundle0015
import Development.EtaleCohomology.EtaleSheaves.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.Bundle0014

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibCovPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.FibCovPf

open LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

theorem qaic_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : QAIC q W') : QAIC q W := by
  obtain ⟨B, i1, i2, I, hB, hq, ⟨e'⟩⟩ := h
  exact ⟨B, i1, i2, I, hB, hq, ⟨e ≪≫ e'⟩⟩

theorem qaic_empty (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (hB : AIC B) (hq : IsUnit (q : B))
    {W : Scheme.{0}} [IsEmpty W] : QAIC q W := by
  have : Subsingleton (B ⧸ (⊤ : Ideal B)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have : IsEmpty (Spec (CommRingCat.of (B ⧸ (⊤ : Ideal B)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (B ⧸ (⊤ : Ideal B))))
  exact ⟨B, inferInstance, inferInstance, ⊤, hB, hq, ⟨isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty⟩⟩

theorem qaic_good (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) (B0 : Type) [CommRing B0]
    [IsDomain B0] (hB0 : AIC B0) (hq0 : IsUnit (q : B0)) {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A))
    (hw : Good w) : QAIC q (pullback w (cpt A)) := by
  rcases hw with hE | ⟨B, i1, i2, i3, hB, e, he⟩
  · have : IsEmpty ↥(pullback w (cpt A) : Scheme.{0}) := ⟨fun x => hE.elim ((pullback.fst w (cpt A)).base x)⟩
    exact qaic_empty q B0 hB0 hq0
  · subst he
    refine ⟨B, i1, i2, (IsLocalRing.maximalIdeal A).map (algebraMap A B), hB, ?_, ?_⟩
    · simpa using hq.map (algebraMap A B)
    · obtain ⟨e2⟩ := fibre_affine A B
      exact ⟨(pullbackRightPullbackFstIso _ (cpt A) e.hom).symm ≪≫ asIso (pullback.snd e.hom _) ≪≫ e2⟩

theorem exists_absolutely_integrally_closed_domain_with_q_unit (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (hZ : AICSch Z) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B), AIC B ∧ IsUnit (q : B) := by
  obtain ⟨hI, hA⟩ := hZ
  obtain ⟨x⟩ : Nonempty Z := hI.nonempty
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : Z.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨Γ(Z, U), inferInstance, IsIntegral.component_integral U, hA U hU ⟨x, hxU⟩, ?_⟩
  have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appLE ⊤ U le_top).hom
  simpa using this

theorem FibCov_of : FibCov := by
  intro q A _ _ hq Z p hZ U V f g _ _ hc hU hV hW
  obtain ⟨B0, _, _, hB0, hq0⟩ := exists_absolutely_integrally_closed_domain_with_q_unit q A hq p hZ
  refine ⟨pullback f (pullback.fst p (cpt A)), pullback g (pullback.fst p (cpt A)),
    pullback.snd f (pullback.fst p (cpt A)), pullback.snd g (pullback.fst p (cpt A)),
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hc, Set.preimage_univ]
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) f) (qaic_good q A hq B0 hB0 hq0 _ hU)
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) g) (qaic_good q A hq B0 hB0 hq0 _ hV)
  · refine qaic_of_iso ?_ (qaic_good q A hq B0 hB0 hq0 _ hW)
    exact pullbackLeftPullbackSndIso f (pullback.fst p (cpt A)) (pullback.snd g (pullback.fst p (cpt A))) ≪≫
      pullback.congrHom rfl pullback.condition.symm ≪≫
      (pullbackLeftPullbackSndIso f g (pullback.fst g (pullback.fst p (cpt A)))).symm ≪≫
      pullbackRightPullbackFstIso g (pullback.fst p (cpt A)) (pullback.snd f g) ≪≫
      pullback.congrHom pullback.condition.symm rfl ≪≫
      pullbackRightPullbackFstIso p (cpt A) (pullback.fst f g ≫ f) ≪≫
      pullback.congrHom (Category.assoc _ _ _) rfl

end LateralTheory.E.FibCovPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibMapRange
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FiberCover
open LateralTheory.E.LineOneCut

lemma fibMap_eq {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fibMap p ι = (pullbackRightPullbackFstIso p (cpt A) ι).inv ≫ pullback.snd ι (pullback.fst p (cpt A)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]; exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]; exact pullback.lift_snd _ _ _

lemma fibMap_open {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z)
    [IsOpenImmersion ι] : IsOpenImmersion (fibMap p ι) := by
  rw [fibMap_eq]; infer_instance

lemma fibMap_range {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    Set.range (fibMap p ι) = (pullback.fst p (cpt A)) ⁻¹' Set.range ι := by
  rw [fibMap_eq, ← Scheme.Pullback.range_snd]
  ext x; constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(pullbackRightPullbackFstIso p (cpt A) ι).hom y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem FibCover_of : FibCover := by
  intro A _ _ Z U V p ι₁ ι₂ h1 h2 hcov
  refine ⟨fibMap_open p ι₁, fibMap_open p ι₂, ?_⟩
  rw [fibMap_range, fibMap_range, ← Set.preimage_union, hcov, Set.preimage_univ]

end LateralTheory.E.FiberCover
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FinOpenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinOpenPf

theorem range_closed (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C)
    (he : IsIdempotentElem e) :
    IsClosed (Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) := by
  rw [PrimeSpectrum.comap_comp, Set.range_comp,
    PrimeSpectrum.localization_away_comap_range (Localization.Away e) e,
    PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (fun x => Algebra.IsIntegral.isIntegral (R := S) x) _
    (PrimeSpectrum.isClosed_zeroLocus _)

theorem FinOpen_of : LateralTheory.E.FinEtSectionPf.FinOpen := by
  intro S C _ _ _ _ e he hoi
  set φ := (algebraMap C (Localization.Away e)).comp (algebraMap S C) with hφ
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap φ)) := hoi.isOpen_range
  obtain ⟨ε, hε, hr⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ⟨range_closed S C e he, hopen⟩
  refine ⟨ε, hε, hr, ?_⟩
  let f := Spec.map (CommRingCat.ofHom φ)
  let g := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away ε)))
  have H : Set.range g ⊆ Set.range f := by
    change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away ε))) ⊆
      Set.range (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away ε) ε, hr]
  let l := IsOpenImmersion.lift f g H
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have key : CommRingCat.ofHom φ ≫ Spec.preimage l =
      CommRingCat.ofHom (algebraMap S (Localization.Away ε)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac f g H
  exact congrArg CommRingCat.Hom.hom key

end LateralTheory.E.FinOpenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.FirstChernNaturality

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  simp [chains, chainsXIso, chainsN, HomologicalComplex.extendMap_f]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem freeGen_nat {P P' : PSh} (g : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R P' U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  unfold freeGen
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P')).app (op U)).hom
    ((((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) = _
  congr 1
  simp only [ModuleCat.freeMk, freeP]
  simp [ModuleCat.free]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl

theorem ev_zpull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (γ : Cocycle ((chains R).obj E') I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1 p s h U x =
      ev γ.1 p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  have hc : (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1.v (-(p : ℤ)) s h =
      ((chains R).map f).f (-(p : ℤ)) ≫ γ.1.v (-(p : ℤ)) s h := by
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by simp) h]
  unfold ev
  rw [hc, ← Category.assoc, chainsXIso_inv_nat, Category.assoc]
  exact congrArg (((chainsXIso R E' p).inv ≫ γ.1.v (-(p : ℤ)) s h).hom.app (op U)).hom
    (freeGen_nat (f.app (op (SimplexCategory.mk p))) U x)

theorem sub_nat {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  unfold Sx.sub
  exact congrFun (congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)) x

theorem lineUnit_comp {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) :
    lineUnit (f ≫ L) x = lineUnit L ((f.app (op (SimplexCategory.mk 1))).app (op U) x) := rfl

theorem etale_first_chern_class_natural_of_spec (hC1 : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle) : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassNaturalUnderPullback := by
  intro q _ E E' f L hinv
  have hinvE : Inv q E := fun U ⟨x⟩ => hinv U ⟨(f.app _).app _ x⟩
  obtain ⟨⟨γ, hγ⟩, h2⟩ := hC1 q L hinv
  rw [h2 γ hγ]
  obtain ⟨_, h2'⟩ := hC1 q (f ≫ L) hinvE
  rw [h2' (zcomp (Cocycle.ofHom ((chains _).map f)) γ (zero_add 2)) ?_]
  · rfl
  obtain ⟨g0, g1, g2⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · intro U x
    rw [ev_zpull]; exact g0 U _
  · intro U x v hv
    rw [ev_zpull]; exact g1 U _ v (by rw [hv, lineUnit_comp])
  · intro U x v w hv hw
    rw [ev_zpull]
    exact g2 U _ v w (by rw [hv, lineUnit_comp, sub_nat]) (by rw [hw, lineUnit_comp, sub_nat])

end LateralTheory.E.FirstChernNaturality
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FracAICPf
section
open Polynomial

namespace LateralTheory.E.FracAICPf

open Classical in
theorem FracAIC_of : LateralTheory.E.ULAStalkPf.FracAIC := by
  intro T K _ _ _ _ _ hT p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T)
    (p.support.image p.coeff)
  set s : K := algebraMap T K b with hs
  have hs0 : s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  set q := p.scaleRoots s with hq
  have hqm : q.Monic := (monic_scaleRoots_iff _).mpr hp
  have hqd : q.natDegree = p.natDegree := natDegree_scaleRoots _ _
  have hlift : q ∈ lifts (algebraMap T K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [hq, coeff_scaleRoots]
    by_cases hi : p.coeff i = 0
    · rw [hi, zero_mul]; exact ⟨0, map_zero _⟩
    have hile : i ≤ p.natDegree := le_natDegree_of_ne_zero hi
    rcases lt_or_eq_of_le hile with hlt | heq
    · obtain ⟨c, hc⟩ := hb (p.coeff i) (Finset.mem_image_of_mem _ (mem_support_iff.mpr hi))
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (b : T) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, Algebra.smul_def, pow_succ, hs]
      ring
    · subst heq
      rw [Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree]
      exact ⟨1, map_one _⟩
  obtain ⟨q', hq'map, hq'deg, hq'm⟩ := lifts_and_natDegree_eq_and_monic hlift hqm
  obtain ⟨r, hr⟩ := hT q' hq'm (by rw [hq'deg, hqd]; exact hdeg)
  refine ⟨algebraMap T K r / s, ?_⟩
  have h1 : q.eval (algebraMap T K r) = 0 := by
    rw [← hq'map, eval_map, eval₂_at_apply, hr, map_zero]
  have h2 := scaleRoots_eval₂_mul (p := p) (RingHom.id K) (algebraMap T K r / s) s
  simp only [RingHom.id_apply, eval₂_id] at h2
  rw [mul_div_cancel₀ _ hs0, ← hq, h1] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hs0)

end LateralTheory.E.FracAICPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlueOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.Gluing₂

theorem orth {S : Type} [CommRing S] : ∀ (n : ℕ) (ε : Fin n → S), (∀ j, IsIdempotentElem (ε j)) →
    ∃ ε' : Fin n → S, OrthogonalIdempotents ε' ∧ (∀ j, ∃ c, ε' j = ε j * c) ∧
      ∑ j, ε' j = 1 - ∏ j, (1 - ε j) := by
  intro n
  induction n with
  | zero => intro ε _; exact ⟨fun _ => 0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩
  | succ n ih =>
    intro ε hε
    obtain ⟨ε₀, ho, hd, hs⟩ := ih (fun j => ε j.succ) (fun j => hε j.succ)
    have ha : IsIdempotentElem (ε 0) := hε 0
    have ha' : IsIdempotentElem (1 - ε 0) := ha.one_sub
    refine ⟨Fin.cons (ε 0) (fun j => (1 - ε 0) * ε₀ j), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simp only [Fin.cons_succ]
        exact ha'.mul (ho.idem j)
    · intro i k hik
      induction i using Fin.cases with
      | zero =>
        induction k using Fin.cases with
        | zero => exact absurd rfl hik
        | succ k =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
      | succ i =>
        induction k using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [mul_comm, ← mul_assoc, mul_sub, mul_one, ha.eq, sub_self, zero_mul]
        | succ k =>
          simp only [Fin.cons_succ]
          have hik' : i ≠ k := fun h => hik (by rw [h])
          calc (1 - ε 0) * ε₀ i * ((1 - ε 0) * ε₀ k) = ((1 - ε 0) * (1 - ε 0)) * (ε₀ i * ε₀ k) := by ring
            _ = 0 := by rw [ho.ortho hik', mul_zero]
    · intro i
      refine Fin.cases ⟨1, by simp⟩ (fun j => ?_) i
      obtain ⟨c, hc⟩ := hd j
      exact ⟨(1 - ε 0) * c, by simp only [Fin.cons_succ, hc]; ring⟩
    · rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Finset.mul_sum, hs]
      ring

theorem glue : LateralTheory.E.FinEtSectionPf.Glue := by
  intro S C _ _ _ n e he hsurj ε hε hr hh
  obtain ⟨ε', ho, hd, hs⟩ := orth n ε hε

  have hf0 : ∏ j, (1 - ε j) = 0 := by
    have hidem : IsIdempotentElem (∏ j, (1 - ε j)) := by
      have := ho.isIdempotentElem_sum (s := Finset.univ).one_sub
      rwa [hs, sub_sub_cancel] at this
    refine hidem.eq_zero_of_isNilpotent ((nilpotent_iff_mem_prime).2 fun J hJ => ?_)
    obtain ⟨q, hq⟩ := hsurj ⟨J, hJ⟩
    have : ∃ j, e j ∉ q.asIdeal := by
      by_contra hall
      push_neg at hall
      exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (he.complete ▸ Ideal.sum_mem _ fun j _ => hall j))
    obtain ⟨j, hj⟩ := this
    have hq' : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away (e j)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (e j)) (e j)]; exact hj
    obtain ⟨q', rfl⟩ := hq'
    have hmem : (⟨J, hJ⟩ : PrimeSpectrum S) ∈ (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S)) := by
      rw [← hr j]; exact ⟨q', by rw [PrimeSpectrum.comap_comp_apply, hq]⟩
    have hεj : ε j ∉ J := hmem
    have h1 : 1 - ε j ∈ J := by
      have : ε j * (1 - ε j) ∈ J := by rw [mul_sub, mul_one, (hε j).eq, sub_self]; exact J.zero_mem
      exact (hJ.mem_or_mem this).resolve_left hεj
    exact J.mem_of_dvd (Finset.dvd_prod_of_mem (fun i => 1 - ε i) (Finset.mem_univ j)) h1
  have hco : CompleteOrthogonalIdempotents ε' := ⟨ho, by rw [hs, hf0, sub_zero]⟩
  choose h hh using hh
  choose c hc using hd
  have hunit : ∀ j, IsUnit (Ideal.Quotient.mk (Ideal.span {1 - ε' j}) (ε j)) := by
    intro j
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ (c j), ?_⟩
    rw [← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_mul, ← hc j, ← (Ideal.Quotient.mk (Ideal.span {1 - ε' j})).map_one, Ideal.Quotient.eq]
    have hm := (Ideal.span {1 - ε' j}).neg_mem (Ideal.mem_span_singleton_self (1 - ε' j))
    rwa [neg_sub] at hm
  let L : ∀ j, Localization.Away (ε j) →+* S ⧸ Ideal.span {1 - ε' j} :=
    fun j => IsLocalization.Away.lift (ε j) (hunit j)
  let Φ : C →+* (∀ j, S ⧸ Ideal.span {1 - ε' j}) :=
    RingHom.pi fun j => ((L j).comp (h j)).comp (algebraMap C (Localization.Away (e j)))
  let E := RingEquiv.ofBijective _ hco.bijective_pi
  have hΦ : ∀ s : S, Φ (algebraMap S C s) = E s := by
    intro s
    funext j
    have := congrArg (fun g => L j (g s)) (hh j)
    simp only [RingHom.comp_apply] at this
    show L j (h j (algebraMap C _ (algebraMap S C s))) = Ideal.Quotient.mk _ s
    rw [this]
    exact IsLocalization.Away.lift_eq (ε j) (hunit j) s
  refine ⟨{ E.symm.toRingHom.comp Φ with commutes' := fun s => ?_ }⟩
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, hΦ]
  simp

theorem Glue_of (_hL : LateralTheory.E.t_E1Cut.EtLift) (_hA : LateralTheory.E.t_E1Cut.EtAIC) : LateralTheory.E.FinEtSectionPf.Glue := glue

end LateralTheory.E.Gluing₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HKCoprodPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.HKCoprodPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {K : ι → CochainComplex C ℤ} (c : Cofan K)
  (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {L : CochainComplex C ℤ}

include hc in
theorem hom_ext_v {p q : ℤ} {a b : c.pt.X p ⟶ L.X q} (h : ∀ j, (c.inj j).f p ≫ a = (c.inj j).f p ≫ b) : a = b :=
  (hc p).hom_ext fun ⟨j⟩ => h j

include hc in
theorem cochain_ext {n : ℤ} {x y : Cochain c.pt L n}
    (h : ∀ j, (Cochain.ofHom (c.inj j)).comp x (zero_add n) = (Cochain.ofHom (c.inj j)).comp y (zero_add n)) : x = y := by
  ext p q hpq
  refine hom_ext_v c hc fun j => ?_
  have := congrArg (fun z => Cochain.v z p q hpq) (h j)
  simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this

def cof (L : CochainComplex C ℤ) {n : ℤ} (b : ∀ j, Cochain (K j) L n) (p q : ℤ) (hpq : p + n = q) :
    Cocone (Discrete.functor K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) p) where
  pt := L.X q
  ι :=
    { app := fun k => (b k.as).v p q hpq
      naturality := by
        rintro ⟨i⟩ ⟨k⟩ ⟨⟨h⟩⟩
        cases h
        exact (Category.id_comp _).trans (Category.comp_id _).symm }

def glue (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {n : ℤ}
    (b : ∀ j, Cochain (K j) L n) : Cochain c.pt L n :=
  Cochain.mk fun p q hpq => (hc p).desc (cof L b p q hpq)

theorem restr_glue {n : ℤ} (b : ∀ j, Cochain (K j) L n) (j : ι) :
    (Cochain.ofHom (c.inj j)).comp (glue c hc b) (zero_add n) = b j := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact (hc p).fac (cof L b p q hpq) ⟨j⟩

include hc in
theorem bij (n : ℤ) : Function.Bijective fun (x : CohomologyClass c.pt L n) (j : ι) =>
    cpre (Cocycle.ofHom (c.inj j)) L n n (zero_add n) x := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    have hj : ∀ j, ∃ β : Cochain (K j) L (n - 1),
        δ (n - 1) n β = (Cochain.ofHom (c.inj j)).comp (x - y : Cocycle c.pt L n).1 (zero_add n) := by
      intro j
      have h := congrFun hxy j
      simp only [cpre_mk] at h
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)] at h
      obtain ⟨β, hβ⟩ := h
      refine ⟨β, ?_⟩
      rw [hβ]
      simp [zcomp, Cochain.comp_sub]
    choose β hβ using hj
    refine ⟨glue c hc β, cochain_ext c hc fun j => ?_⟩
    rw [← δ_ofHom_comp, restr_glue, hβ]
  · intro y
    choose z hz using fun j => (y j).mk_surjective
    have hδ : δ n (n + 1) (glue c hc fun j => (z j).1) = 0 := cochain_ext c hc fun j => by
      rw [← δ_ofHom_comp, restr_glue, Cocycle.δ_eq_zero]; simp
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hδ), funext fun j => ?_⟩
    simp only [cpre_mk]
    rw [← hz j]
    congr 1
    exact Cocycle.ext (restr_glue c hc (fun j => (z j).1) j)

end General

set_option synthInstance.maxHeartbeats 400000 in
theorem HKCoprod_of : LateralTheory.E.CoprodPf.HKCoprod := by
  intro R _ ι K c hc F n
  have h1 : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits.{1} (Shv R)
  have h0 : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} (Shv R)
  have : HasColimitsOfShape (Discrete ι) (Shv R) := inferInstance
  exact bij c (fun p => isColimitOfPreserves (HomologicalComplex.eval _ _ p) hc) n

end LateralTheory.E.HKCoprodPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HensCut
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.HensCut

def LocAIC : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B), (0 : B) ∉ M → AIC B →
  IsDomain (Localization M) ∧ AIC (Localization M)

def MonicSplits : Prop := ∀ (R : Type) [CommRing R] [IsDomain R], AIC R → ∀ p : Polynomial R, p.Monic →
  ∃ s : Multiset R, p = (s.map fun a => Polynomial.X - Polynomial.C a).prod

def IdemPart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ) (y : Fin n → A), ∏ l, y l = 0 →
  IsUnit (∑ l, ∏ m ∈ Finset.univ.erase l, y m) →
  ∃ e : Fin n → A, (∀ l, IsIdempotentElem (e l)) ∧ (∀ l m, l ≠ m → e l * e m = 0) ∧ ∑ l, e l = 1 ∧ ∀ l, e l * y l = 0

def ColimHens : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) (c : Cocone D), IsColimit c →
  (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) →
  (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) →
  (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
    IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
    ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧ a - (D.map f).hom a₀ ∈ I.map (β.app j').hom) →
  ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

def PartDiag : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) ∧
    (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) ∧
    (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
      IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
      ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧
        a - (D.map f).hom a₀ ∈ I.map (β.app j').hom)

theorem goal_of (_hL : LocAIC) (_hM : MonicSplits) (_hI : IdemPart) (hC : ColimHens) (hD : PartDiag) :
    LateralTheory.E.QuotAcycCut.Hens := by
  intro q B _ _ I hB hq
  obtain ⟨J, _, _, D, β, hst, ha, hb, hc⟩ := hD q B I hB hq
  obtain ⟨K, hK, he⟩ := hC B I J D β (colimit.cocone D) (colimit.isColimit D) ha hb hc
  refine ⟨J, inferInstance, inferInstance, D, colimit.cocone D, colimit.isColimit D, hst, ?_, K, hK, he⟩
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have h1 : IsUnit ((q : B)) := hq
  have h2 := h1.map ((β.app j) ≫ (colimit.cocone D).ι.app j).hom
  simpa using h2

end LateralTheory.E.HensCut
end
end

