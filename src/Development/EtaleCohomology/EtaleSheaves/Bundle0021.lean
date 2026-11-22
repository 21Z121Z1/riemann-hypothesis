import Development.EtaleCohomology.EtaleSheaves.Bundle0015
import Development.EtaleCohomology.EtaleSheaves.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.EtaleCohomology.EtaleSheaves.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.EtaleCohomology.EtaleSheaves.Bundle0013

-- bundled from Development.EtaleCohomology.EtaleSheaves.IECobPf
section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IECobPf

theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

theorem IECob_of : LateralTheory.E.ULAStalkPf.IECob := by
  intro A B C D f g u v sq hf
  have := et_cobase
  have hI : IE.IsStableUnderCobaseChange := by
    unfold IE; infer_instance
  exact hI.of_isPushout sq.flip hf

end LateralTheory.E.IECobPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ImgOf
section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.ImgPf

theorem Img_of : LateralTheory.E.ChowCut.Img := by
  intro A _ Z X h p _ hh hZ
  have := hh
  have := hZ
  have : QuasiCompact h := inferInstance
  have : IsIntegralHom (h.toImage ≫ h.imageι) := by rw [Scheme.Hom.toImage_imageι]; exact hh
  refine ⟨h.image, h.toImage, h.imageι ≫ p, inferInstance, inferInstance,
    IsIntegralHom.of_comp h.toImage h.imageι, inferInstance, ?_⟩
  rw [Scheme.Hom.toImage_imageι_assoc]

end LateralTheory.E.ImgPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntFibPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntFibPf

lemma eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

lemma eqv_iso {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

lemma isPushout_quot (A : Type) [CommRing A] [IsLocalRing A] {B : CommRingCat.{0}} (ψ : CommRingCat.of A ⟶ B) :
    IsPushout ψ (CommRingCat.ofHom (IsLocalRing.residue A))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map
        : IsLocalRing.ResidueField A →+* _)) := by
  have w : CommSq ψ (CommRingCat.ofHom (IsLocalRing.residue A)) (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map : IsLocalRing.ResidueField A →+* _)) := by
    constructor; ext a; rfl
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
      (Ideal.Quotient.lift ((IsLocalRing.maximalIdeal A).map ψ.hom) s.inl.hom ?_)) ?_ ?_ ?_)
  · rename_i s; intro a ha
    have hle : ((IsLocalRing.maximalIdeal A).map ψ.hom) ≤ RingHom.ker s.inl.hom := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
      have h1 := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
      simp only [Ideal.mem_comap, RingHom.mem_ker, h1,
        (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
    exact hle ha
  · intro s; ext b; rfl
  · intro s; ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have h1 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    exact h1
  · intro s m h1 h2
    ext b
    have := congrArg (fun f => f.hom b) h1
    exact this

theorem IntFib_of : LateralTheory.E.IntPBPf.IntFib := by
  intro A _ _ X p hp
  have : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, ?_, ?_⟩
  · rw [← IsIntegralHom.SpecMap_iff, hψ]; infer_instance
  · intro q i h
    have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot A ψ)
    have hP' : IsPullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom))) ≫ X.isoSpec.inv) _ p
        (LateralTheory.E.t_E2Cut.cpt A) :=
      hP.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by simp [hψ]) (by simp)
    rw [← hP'.isoPullback_inv_fst, Functor.map_comp, Functor.map_comp]
    exact eqv_comp _ _ _ (eqv_iso (sch.mapIso hP'.isoPullback.symm) _)
      (eqv_comp _ _ _ h (eqv_iso (sch.mapIso X.isoSpec.symm) _))

end LateralTheory.E.IntFibPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntHensPf
section
noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.IntHensPf

theorem mem_sub (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (m : Ideal A) (S : Subalgebra A B)
    {n : ℕ} (c : Fin n → B) (g : Fin n → (algebraMap A B '' (m : Set A))) (hc : ∀ i, c i ∈ S) :
    ∃ y ∈ m.map (algebraMap A S), (y : B) = ∑ i, c i • (g i : B) := by
  choose a ha hag using fun i => (g i).2
  refine ⟨∑ i, ⟨c i, hc i⟩ * algebraMap A S (a i), Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i)), ?_⟩
  change S.val _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, smul_eq_mul, ← hag]; rfl

theorem jac (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B] [Algebra.IsIntegral A B] :
    (maximalIdeal A).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro n ⟨-, hn⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (n.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n
  exact le_of_eq (IsLocalRing.eq_maximalIdeal this).symm

theorem evalS (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Subalgebra A B) (p : S[X]) (y : S) :
    ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := by
  rw [eval_map]; exact (eval₂_hom S.val.toRingHom y).symm

theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Algebra A B]
    [Algebra.IsIntegral A B] : HenselianRing B ((maximalIdeal A).map (algebraMap A B)) := by
  classical
  refine ⟨jac A B, fun f hf a0 h0 h1 => ?_⟩
  set J := (maximalIdeal A).map (algebraMap A B) with hJ
  obtain ⟨n1, c1, g1, hs1⟩ := Submodule.mem_span_set'.1 h0
  obtain ⟨v, hv⟩ := h1.exists_left_inv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hu : u * f.derivative.eval a0 - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
  obtain ⟨n2, c2, g2, hs2⟩ := Submodule.mem_span_set'.1 hu
  set s : Finset B := insert a0 (insert u (f.coeffs ∪ (Finset.univ.image c1 ∪ Finset.univ.image c2)))
  let S := Algebra.adjoin A (s : Set B)
  have hsS : ∀ x ∈ s, x ∈ S := fun x hx => Algebra.subset_adjoin hx
  haveI : Module.Finite A S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)
  let JS := (maximalIdeal A).map (algebraMap A S)
  haveI : HenselianRing S JS := GlobalTheory.henselianRing_of_finite A JS (GlobalTheory.map_maximalIdeal_le_jacobson_of_finite A S)
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc => hsS c (by simp [s, Finset.mem_coe.1 hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, hsS a0 (by simp [s])⟩
  let uS : S := ⟨u, hsS u (by simp [s])⟩
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  have h0S : g.eval b0 ∈ JS := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c1 g1 (fun i => hsS _ (by simp [s]))
    convert hy using 1
    apply Subtype.ext
    rw [hyv, hs1, evalS, hgf]
  have h1S : IsUnit (Ideal.Quotient.mk JS (g.derivative.eval b0)) := by
    obtain ⟨y, hy, hyv⟩ := mem_sub A B _ S c2 g2 (fun i => hsS _ (by simp [s]))
    have : uS * g.derivative.eval b0 - 1 ∈ JS := by
      convert hy using 1
      apply Subtype.ext
      rw [hyv, hs2]
      simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one, evalS]
      rw [← derivative_map, hgf]
    rw [← Ideal.Quotient.eq, map_mul, map_one] at this
    exact ⟨⟨_, _, (mul_comm _ _).trans this, this⟩, rfl⟩
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian g hgm b0 h0S h1S
  refine ⟨(a : B), ?_, ?_⟩
  · rw [IsRoot.def, ← hgf, ← evalS, ha.eq_zero]; rfl
  · have := Ideal.mem_map_of_mem S.val.toRingHom ha'
    rw [Ideal.map_map] at this
    simpa using this

theorem IntHens_of : LateralTheory.E.IntPBPf.IntHens := by
  intro A B _ _ _ φ hφ
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  exact hens A B

end LateralTheory.E.IntHensPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IntegralNormalization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf

def OpenNbhdIC : Prop := ∀ {Z : Scheme.{0}} (U : Z.Opens), AICSch Z → (U : Set Z).Nonempty → AICSch U.toScheme

def FFAlg : Prop := ∀ {Z : Scheme.{0}} [IsIntegral Z], AICSch Z → IsAlgClosed Z.functionField

def NormAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W)
  [QuasiCompact g] [QuasiSeparated g], AICSch g.normalization

theorem spec_field_qc (K : Type) [Field K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W) : QuasiCompact g := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U _
  exact (Set.toFinite _).isCompact

theorem Norm_of (h0 : OpenNbhdIC) (h1 : FFAlg) (h2 : NormAIC) : LateralTheory.E.ChowCut.Norm := by
  intro Z W f _ hZ ⟨U, s, hU, hs⟩
  have : IsIntegral Z := hZ.1
  have hUa := h0 U hZ hU
  have := hUa.1
  have := h1 hUa
  let g0 : Spec (CommRingCat.of U.toScheme.functionField) ⟶ U.toScheme := U.toScheme.fromSpecStalk _
  let g := g0 ≫ s
  have := spec_field_qc _ g
  refine ⟨g.normalization, g.fromNormalization, inferInstance, h2 _ g, ?_⟩
  have hg0 : IsDominant g0 := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.range_fromSpecStalk]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec U.toScheme).def ▸ closure_mono (Set.singleton_subset_iff.mpr (specializes_refl _)))
  have hU' : IsDominant U.ι := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.Opens.range_ι]
    exact (U.isOpen.dense hU).closure_eq
  have e : g.toNormalization ≫ g.fromNormalization ≫ f = g0 ≫ U.ι := by
    rw [reassoc_of% g.toNormalization_fromNormalization, Category.assoc, hs]
  have : IsDominant (g.toNormalization ≫ g.fromNormalization ≫ f) := by rw [e]; infer_instance
  exact IsDominant.of_comp g.toNormalization _

end LateralTheory.E.NormPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCBijPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCBijPf

def TwGenNZAC : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (K : Type) [Field K] [IsAlgClosed K] (ζ : Prim q K) (c : ZMod q),
  c.val • twGen i (gam ζ) = 0 → c = 0

abbrev TwGenNZ : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (B : Type) [CommRing B] [Nontrivial B] (ζ : Prim q B) (c : ZMod q),
  c.val • twGen i (gam ζ) = 0 → c = 0

def LCSurj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B), Function.Surjective (m B ζ)

theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold Sec.res twGen ofRings.sec tw ofRings
  erw [← ModuleCat.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g.op).hom) (Finsupp.single ζ 1)) = _
  erw [Finsupp.mapDomain_single]
  rfl

theorem gam_map {q : ℕ} {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) :
    gam (ζ.map f) = (gam ζ).map (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  apply Subtype.ext
  change (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (f ζ.1) =
    (Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ζ.1)
  have := congrArg (fun φ => φ.hom ζ.1) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem twGenNZ_of (hAC : TwGenNZAC) : TwGenNZ := by
  intro q _ i B _ _ ζ c h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  let _ : Field (B ⧸ M) := Ideal.Quotient.field M
  let f : B →+* AlgebraicClosure (B ⧸ M) := (algebraMap (B ⧸ M) (AlgebraicClosure (B ⧸ M))).comp (Ideal.Quotient.mk M)
  apply hAC q i (AlgebraicClosure (B ⧸ M)) (ζ.map f) c
  have h2 := congrArg (Sec.res (Spec.map (CommRingCat.ofHom f))) h
  have hs : ∀ x : Sec (tw q i) (Spec (CommRingCat.of B)), Sec.res (Spec.map (CommRingCat.ofHom f)) (c.val • x) =
      c.val • Sec.res (Spec.map (CommRingCat.ofHom f)) x := fun x => map_nsmul _ _ x
  have hz : Sec.res (Spec.map (CommRingCat.ofHom f)) (0 : Sec (tw q i) (Spec (CommRingCat.of B))) = 0 := map_zero _
  rw [hs, hz, twGen_res, ← gam_map] at h2
  exact h2

theorem lcInj (hT : TwGenNZ) (q : ℕ) [NeZero q] (i : ℤ) m (hm : IsLCMap q i m) (B : Type) [CommRing B]
    (ζ : Prim q B) : Function.Injective (m B ζ) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  by_contra hne
  obtain ⟨p, hp⟩ : ∃ p, φ p ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LocallyConstant.ext h)
  set c := φ p with hc
  let U : Set (PrimeSpectrum B) := φ ⁻¹' {c}
  have hU : IsClosed U := (φ.isLocallyConstant.isClopen_fiber c).isClosed
  let I := PrimeSpectrum.vanishingIdeal U
  let f := Ideal.Quotient.mk I
  have hrange : Set.range (PrimeSpectrum.comap f) = U := by
    rw [_root_.range_comap_of_surjective _ f Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.closure_eq]
  have hconst : lcMap f φ = LocallyConstant.const _ c := by
    ext x
    have : PrimeSpectrum.comap f x ∈ U := hrange ▸ ⟨x, rfl⟩
    exact this
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h ▸ Submodule.mem_top
    have hpU : p ∈ U := rfl
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ((PrimeSpectrum.mem_vanishingIdeal _ _).1 h1 p hpU))
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have h1 := hm.1 B (B ⧸ I) f ζ φ
  rw [hφ, hconst, hm.2] at h1
  simp only [map_zero] at h1
  exact hp (hT q i (B ⧸ I) (ζ.map f) c h1.symm)

theorem LCBij_of (hT : TwGenNZAC) (hS : LCSurj) : LateralTheory.E.LocallyConstantH0.LCBij :=
  fun q _ i m hm B _ ζ => ⟨lcInj (twGenNZ_of hT) q i m hm B ζ, hS q i m hm B ζ⟩

end LateralTheory.E.LCBijPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LCMapPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCMapPf

def TwNat : Prop := ∀ (q : ℕ) (i : ℤ) (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
  Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)

def LCSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (Y : Type)
  (φ : LocallyConstant (PrimeSpectrum B) Y) (a b : Sec F (Spec (CommRingCat.of B))),
  (∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : Y), (∀ v : V, φ (g.base v) = c) → Sec.res g a = Sec.res g b) → a = b

def LCGlue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (Y : Type)
  (φ : LocallyConstant (PrimeSpectrum B) Y) (s : Y → Sec F (Spec (CommRingCat.of B))),
  ∃ t : Sec F (Spec (CommRingCat.of B)), ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : Y),
    (∀ v : V, φ (g.base v) = c) → Sec.res g t = Sec.res g (s c)

theorem twNat : TwNat := by
  intro q i V U g ζ
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op
  have h2 := congrArg (fun k => k.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))) h
  simp only [ModuleCat.hom_comp] at h2
  simp only [LinearMap.coe_comp] at h2
  unfold twGen ofRings.sec
  refine h2.symm.trans (congrArg ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom ?_)
  simp only [twF, Functor.comp_map]
  rw [ModuleCat.hom_ofHom]
  first
  | (erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; done)
  | (erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  | exact congrArg (Submodule.Quotient.mk (p := twRel q i _)) (Finsupp.mapDomain_single (f := Prim.map g.appTop.hom) (a := ζ) (b := (1 : ULift (ZMod q))))

theorem nsmul_val {q : ℕ} [NeZero q] (i : ℤ) (U : Scheme.{0}) (x : Sec (tw q i) U) (c : ZMod q) :
    c.val • x = (ULift.up c : ULift (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift (ZMod q))]
  congr 1
  ext
  exact (ULift.down_natCast _).trans (ZMod.natCast_zmod_val c)

def sG {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B) (c : ZMod q) : Sec (tw q i) (Spec (CommRingCat.of B)) :=
  (ULift.up c : ULift (ZMod q)) • twGen i (gam ζ)

theorem res_smul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift R) (x : Sec F U) :
    Sec.res g (r • x) = r • Sec.res g x := by
  simp [Sec.res]

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := by
  simp [Sec.res]

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

def tG (hG : LCGlue) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)) :
    Sec (tw q i) (Spec (CommRingCat.of B)) :=
  Classical.choose (hG (ZMod q) (tw q i) B (ZMod q) φ (sG i ζ))

theorem tG_spec (hG : LCGlue) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B)
    (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)) (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : ZMod q)
    (h : ∀ v : V, φ (g.base v) = c) : Sec.res g (tG hG i ζ φ) = Sec.res g (sG i ζ c) :=
  Classical.choose_spec (hG (ZMod q) (tw q i) B (ZMod q) φ (sG i ζ)) V g c h

theorem tG_add (hG : LCGlue) (hS : LCSep) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B)
    (φ ψ : LocallyConstant (PrimeSpectrum B) (ZMod q)) : tG hG i ζ (φ + ψ) = tG hG i ζ φ + tG hG i ζ ψ := by
  let χ : LocallyConstant (PrimeSpectrum B) (ZMod q × ZMod q) :=
    ⟨fun x => (φ x, ψ x), IsLocallyConstant.comp₂ φ.2 ψ.2 Prod.mk⟩
  refine hS (ZMod q) (tw q i) B _ χ _ _ ?_
  intro V g c hc
  have h1 : ∀ v : V, φ (g.base v) = c.1 := fun v => congrArg Prod.fst (hc v)
  have h2 : ∀ v : V, ψ (g.base v) = c.2 := fun v => congrArg Prod.snd (hc v)
  have h3 : ∀ v : V, (φ + ψ) (g.base v) = c.1 + c.2 := fun v => by
    show φ (g.base v) + ψ (g.base v) = _
    rw [h1, h2]
  rw [tG_spec hG i ζ _ V g _ h3, res_add, tG_spec hG i ζ _ V g _ h1, tG_spec hG i ζ _ V g _ h2, ← res_add]
  congr 1
  unfold sG
  rw [← add_smul]
  rfl

theorem LCMap_of_parts (hT : TwNat) (hS : LCSep) (hG : LCGlue) : LCMap := by
  intro q _ i
  refine ⟨fun B _ ζ => AddMonoidHom.mk' (tG hG i ζ) (tG_add hG hS i ζ), ?_, ?_⟩
  · intro B C _ _ f ζ φ
    change Sec.res _ (tG hG i ζ φ) = tG hG i (ζ.map f) (lcMap f φ)
    refine hS (ZMod q) (tw q i) C _ (lcMap f φ) _ _ ?_
    intro V g c hc
    have hc' : ∀ v : V, φ ((g ≫ Spec.map (CommRingCat.ofHom f)).base v) = c := fun v => by
      exact hc v
    rw [← res_comp, tG_spec hG i ζ φ V _ c hc', tG_spec hG i (ζ.map f) _ V g c hc]
    unfold sG
    rw [res_smul, res_smul, hT, hT]
    have hP : Prim.map (g ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom (gam ζ) = Prim.map g.appTop.hom (gam (ζ.map f)) := by
      apply Subtype.ext
      change (g ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ζ.1) =
        g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (f ζ.1))
      have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      congr 1
      rw [← CommRingCat.comp_apply, ← hn]
      rfl
    rw [hP]
  · intro B _ ζ c
    change tG hG i ζ _ = _
    have h := tG_spec hG i ζ (LocallyConstant.const _ c) _ (𝟙 _) c (fun v => rfl)
    rw [res_id, res_id] at h
    rw [h, nsmul_val]
    rfl

def fibS (B : Type) [CommRing B] {Y : Type} (φ : LocallyConstant (PrimeSpectrum B) Y) : Sieve (Spec (CommRingCat.of B)) where
  arrows V g := ∃ c, ∀ v : V, φ (g.base v) = c
  downward_closed := by
    rintro V W g ⟨c, hc⟩ k
    exact ⟨c, fun w => hc (k.base w)⟩

theorem fibS_mem (B : Type) [CommRing B] {Y : Type} (φ : LocallyConstant (PrimeSpectrum B) Y) :
    fibS B φ ∈ Scheme.etaleTopology (Spec (CommRingCat.of B)) := by
  refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).mpr ?_
  let O : PrimeSpectrum B → (Spec (CommRingCat.of B)).Opens := fun x =>
    ⟨φ ⁻¹' {φ x}, φ.isLocallyConstant.isOpen_fiber _⟩
  refine ⟨Scheme.Cover.mkOfCovers (PrimeSpectrum B) (fun x => (O x).toScheme) (fun x => (O x).ι)
    (fun x => ⟨x, ⟨x, rfl⟩, by simp⟩), ?_⟩
  rintro _ _ ⟨x⟩
  refine ⟨φ x, fun v => ?_⟩
  have hv := v.2
  first
  | exact hv
  | (simp only [Scheme.Cover.mkOfCovers_f, Scheme.Opens.ι_apply]; exact hv)
  | (simp [O, Scheme.Cover.mkOfCovers_f] at hv ⊢; exact hv)

theorem isSheafT {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property

theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (Z : Scheme.{0}) [IsEmpty Z] (a b : Sec F Z) : a = b :=
  ((isSheafT F) _ (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext (fun _ _ h => h.elim)

theorem lcSep : LCSep := by
  intro R _ F B _ Y φ a b h
  exact ((isSheafT F) _ (fibS_mem B φ)).isSeparatedFor.ext (fun V g hg => h V g hg.choose hg.choose_spec)

theorem lcGlue : LCGlue := by
  intro R _ F B _ Y φ s
  let x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (fibS B φ).arrows :=
    fun V g hg => Sec.res g (s hg.choose)
  have key : ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c d : Y), (∀ v : V, φ (g.base v) = c) →
      (∀ v : V, φ (g.base v) = d) → Sec.res g (s c) = Sec.res g (s d) := by
    intro V g c d hc hd
    by_cases hV : Nonempty V
    · obtain ⟨v⟩ := hV
      rw [← hc v, ← hd v]
    · have : IsEmpty V := not_nonempty_iff.1 hV
      exact sec_empty F V _ _
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    change Sec.res (k ≫ g) (s _) = Sec.res k (Sec.res g (s _))
    rw [← res_comp]
    exact key W (k ≫ g) _ _ ((fibS B φ).downward_closed hg k).choose_spec (fun w => hg.choose_spec (k.base w))
  obtain ⟨t, ht, -⟩ := (isSheafT F) _ (fibS_mem B φ) x hx
  refine ⟨t, fun V g c hc => ?_⟩
  have h1 := ht g ⟨c, hc⟩
  refine h1.trans (key V g _ _ (Exists.choose_spec (p := fun c => ∀ v : V, φ (g.base v) = c) ⟨c, hc⟩) hc)

theorem LCMap_of : LCMap := LCMap_of_parts twNat lcSep lcGlue

end LateralTheory.E.LCMapPf
end
end

