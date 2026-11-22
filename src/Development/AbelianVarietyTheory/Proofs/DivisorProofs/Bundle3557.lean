import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3545
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3501
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3539
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegrals
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem exists_isMix_of_arch : ArchInteg → ArchRecip →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  intro hI hR
  have key : ∀ m : ℕ, ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T := by
    intro m
    induction m with
    | zero => intro k _ Y q _; exact ⟨_, isMix_zero q⟩
    | succ m ih => exact GlobalTheory.T.isMixedHeightByInduction_succ hI hR m ih
  intro k _ Y q h m
  exact key m k Y q h

end GlobalTheory.MixHt

example : ArchInteg → ArchRecip → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) :=
  GlobalTheory.MixHt.exists_isMix_of_arch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFamThrough
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartTrait

theorem exists_cdvr_through {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [IsLocallyNoetherian S] (x : S) (hx : x ∉ Set.range j) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ S) (y₀ : Sp (FractionRing W) ⟶ U),
      y₀ ≫ j = jK W ≫ a ∧ a (closedPoint W) = x := by
  have : IsDominant j := ⟨hd⟩
  let O := S.presheaf.stalk x
  obtain ⟨ge, hge, hs⟩ := exists_mem_genericPoints_specializes x
  have hge' := genericPoints_subset_range_of_isDominant j hge
  have h1 : ge ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hs
  obtain ⟨q, rfl⟩ := h1
  have hop : IsOpen (S.fromSpecStalk x ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage (S.fromSpecStalk x).continuous
  obtain ⟨_, ⟨f, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) hge' hop
  have hfm : f ∈ maximalIdeal O := by
    by_contra hn
    have : S.fromSpecStalk x (closedPoint O) ∈ Set.range j :=
      hf (show closedPoint O ∈ PrimeSpectrum.basicOpen f from hn)
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact hx this
  let Ω := AlgebraicClosure (ResidueField O)
  let φ : O →+* Ω := (algebraMap (ResidueField O) Ω).comp (residue O)
  have : IsLocalHom φ := ⟨fun a ha => by
    by_contra h
    have : residue O a = 0 := (residue_eq_zero_iff a).2 h
    simp [φ, this] at ha⟩
  obtain ⟨W, _, _, _, _, ψ, ιW, hψ, hιW⟩ := GlobalTheory.GeomTrait.exists_dvr (O := O) (Ω := Ω) hfm q.asIdeal q.isPrime hqf φ
  let a : Sp W ⟶ S := Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecStalk x
  obtain ⟨y, hy⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset j
    (spMap (algebraMap W (FractionRing W)) ≫ a) (by
      rintro _ ⟨t, rfl⟩
      have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
      rw [Scheme.Hom.comp_apply, this]
      exact hf (a := PrimeSpectrum.comap ψ ⊥) hψ)
  have hloc : IsLocalHom ψ := ⟨fun r hr => by
    by_contra h
    have h2 : φ r = ιW (residue W (ψ r)) := by rw [← hιW]; rfl
    have : residue W (ψ r) ≠ 0 := by
      rw [Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]; exact hr
    have h3 : φ r ≠ 0 := by rw [h2]; exact (map_ne_zero ιW).2 this
    exact h (isUnit_of_map_unit φ r (IsUnit.mk0 _ h3))⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, a, y, hy, ?_⟩
  change S.fromSpecStalk x (Spec.map (CommRingCat.ofHom ψ) (closedPoint W)) = x
  have : Spec.map (CommRingCat.ofHom ψ) (closedPoint W) = closedPoint O :=
    IsLocalRing.comap_closedPoint ψ
  rw [this, Scheme.fromSpecStalk_closedPoint]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem trait_be_pos (T : UPoinc.UTrait Xo c) {x : T.P.D.toPre.X} (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨i, hi⟩ := IsMonomial.exists_pos (maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases i
  exact hi

theorem trait_finrank_le {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    {y : Sp (FractionRing R) ⟶ Xo.XF c} {t : SAB H (Sp R)} (hg : UPoinc.GenOf Xo c y t) (P : PELUnif (maximalIdeal R) t) :
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q := by
  obtain ⟨tK, ⟨m⟩, ⟨m'⟩⟩ := hg
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Sp (FractionRing R) := spMap (algebraMap (FractionRing R) K)
  have hx : x' ≫ jK R = spMap f := by
    rw [← GlobalTheory.TorRef.DomFine.spMap_comp']
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective ((x' ≫ y ≫ pullback.fst _ _) ≫ Xo.s)
  have hdet := (Xo.univ.geom K (x' ≫ y ≫ pullback.fst _ _) β₀.hom hβ₀.symm).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act (x' ≫ y ≫ pullback.fst _ _) τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m'.cart tK.act Xo.univ.t.act m'.act x' τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart tK.act t.act m.act x' τ N).1 h₅
    rw [hx] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem bal_diag_eq {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms (H.bar : 𝓞 E → 𝓞 E) X) (y : X) : β y y = 2 * β (H.w0 • y) y := by
  obtain ⟨h1, h2⟩ := hβ
  have h := h2 H.w0 y y
  rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_smul, one_smul, map_sub, h1 y (H.w0 • y)] at h
  linarith

theorem spMap_sq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] (f : A →+* B) (g : A →+* C)
    (f' : B →+* D) (g' : C →+* D) (h : ∀ a, f' (f a) = g' (g a)) : spMap f' ≫ spMap f = spMap g' ≫ spMap g := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact h a

theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem exists_monoFam_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hnsi Z zs i OZ N d J S π j _ BD hU hsep x hx
  obtain ⟨⟨-, -, -, -, hizs, -, -⟩, -, -, -, ⟨-, hproj, -, hdense, hjπ, -, -, -⟩, -⟩ := hU
  haveI : LocallyOfFiniteType (π ≫ zs) := GlobalTheory.T.locallyOfFiniteType_of_isProjOver c.F S (π ≫ zs) hproj
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨W, _, _, _, _, a, y₀, hy₀, hax⟩ := exists_cdvr_through j hdense x hx
  let b₀ : c.F →+* W := (Spec.preimage (a ≫ π ≫ zs)).hom
  have hb₀ : spMap b₀ = a ≫ π ≫ zs := Spec.map_preimage _
  haveI : CharZero W := charZero_of_injective_ringHom b₀.injective
  have hW : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨T, f₁, fK₁, -, hloc₁, -, hc₁, hTy⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c W hW inferInstance y₀

  haveI := hloc₁
  obtain ⟨_, _, _⟩ := T.cdvr
  haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
  haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hpolT : IsPolFanOn (H.bar : 𝓞 E → 𝓞 E) φ T.P.D.toPre.X := hpol _ (trait_finrank_le T.gen T.P)
  have hbal : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X :=
    (balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev
  obtain ⟨r, gm, k, cc, hgm, hk, hcc, hsum⟩ := GlobalTheory.Poinc.Cover.exists_cone (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) φ
    T.P.D.toPre.X hpolT T.be hbal (fun y hy => trait_be_pos T hy)
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨T₂, g, gK, e, q, -, hgloc, hgK, hT₂y, hq, hbe⟩ := GlobalTheory.T.exists_unitaryTrait_ramifiedExtension_form_multiple T (k * l.M') (Nat.mul_pos hk hM)
  haveI := hgloc
  obtain ⟨_, _, _⟩ := T₂.cdvr

  have hW₁ : spMap fK₁ ≫ jK W = jK T.V ≫ spMap f₁ := spMap_sq (algebraMap W _) f₁ fK₁ (algebraMap T.V _) hc₁
  have hT₁ : spMap gK ≫ jK T.V = jK T₂.V ≫ spMap g := spMap_sq (algebraMap T.V _) g gK (algebraMap T₂.V _) hgK
  have hy0s : y₀ ≫ pullback.snd _ _ = jK W ≫ spMap b₀ := by
    rw [hb₀, ← hizs, ← hjπ]
    simp only [Category.assoc]
    rw [reassoc_of% hy₀]
  let bb : c.F →+* T₂.V := g.comp (f₁.comp b₀)
  have hover : T₂.y ≫ pullback.snd _ _ = jK T₂.V ≫ spMap bb := by
    rw [hT₂y, hTy]
    simp only [Category.assoc]
    rw [hy0s, reassoc_of% hW₁, reassoc_of% hT₁]
    simp only [bb, spMap_comp_, Category.assoc]
  have hev : ∀ i z, gm i z z = 2 * gm i (H.w0 • z) z := fun i z => bal_diag_eq (hgm.mem i) z
  have hnn : ∀ i z, 0 ≤ gm i (H.w0 • z) z := fun i z => by
    have := hgm.nonneg i z
    rw [hev] at this
    omega
  have hsumz : ∀ z, (k : ℤ) * T.be z z = ∑ i, (cc i : ℤ) * gm i z z := fun z => by
    have := congrArg (fun β : LinearMap.BilinForm ℤ T.P.D.toPre.X => β z z) hsum
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hmono : IsMonomial T₂.P.D.toPre (fun i => T₂.ϖ ^ (q * cc i))
      (fun i => (l.M' : ℤ) • pull e.symm.toLinearMap (gm i)) := by
    intro y
    obtain ⟨u, n₀, hn₀, hψ⟩ := T₂.mono y
    have hy : y = e (e.symm y) := (e.apply_symm_apply y).symm
    set z := e.symm y
    refine ⟨u, fun i => (l.M' * gm i (H.w0 • z) z).toNat, fun i => ?_, ?_⟩
    · simp only [LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, smul_eq_mul]
      rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z)), hev]
      ring
    · convert hψ using 2
      rw [Fin.prod_univ_one]
      simp only [Matrix.cons_val_zero, ← pow_mul, Finset.prod_pow_eq_pow_sum]
      congr 1
      have h0 : T₂.be y y = 2 * n₀ 0 := by simpa using hn₀ 0
      rw [hy, hbe] at h0
      have hz := hsumz z
      have hcast : ((∑ i, q * cc i * (l.M' * gm i (H.w0 • z) z).toNat : ℕ) : ℤ) =
          ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z))]
      have hz2 : (k : ℤ) * T.be z z = 2 * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z := by
        rw [hz, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hev]
        ring
      have hS : ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) =
          (q * l.M') * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have h2 : (2 : ℤ) * (∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z)) = 2 * (n₀ 0 : ℤ) := by
        rw [← h0, hS]
        push_cast
        linear_combination (-((q : ℤ) * l.M')) * hz2
      have h3 := mul_left_cancel₀ (two_ne_zero) h2
      exact_mod_cast hcast.trans h3
  let C : MonoFam Xo c φ T₂.V :=
    { b := bb, t := T₂.t, P := T₂.P, y := T₂.y, y_over := hover, gen := T₂.gen, m := r,
      s := fun i => T₂.ϖ ^ (q * cc i),
      s_mem := fun i => Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 T₂.irr.not_isUnit) _
        (Nat.mul_pos hq (hcc i)),
      δ := fun i => pull e.symm.toLinearMap (gm i), cone := hgm.pull_equiv e.symm,
      rank := trait_finrank_le T₂.gen T₂.P, mono := hmono }
  have hcomp : C.y ≫ j = jK T₂.V ≫ (spMap (g.comp f₁) ≫ a) := by
    show T₂.y ≫ j = _
    rw [hT₂y, hTy]
    simp only [Category.assoc]
    rw [hy₀, reassoc_of% hW₁, reassoc_of% hT₁, spMap_comp_]
    simp only [Category.assoc]
  have hcl : (spMap (g.comp f₁) ≫ a) (closedPoint T₂.V) = x := by
    have h1 : spMap (g.comp f₁) (closedPoint T₂.V) = closedPoint W := IsLocalRing.comap_closedPoint (g.comp f₁)
    change a (spMap (g.comp f₁) (closedPoint T₂.V)) = x
    rw [h1, hax]
  exact ⟨T₂.V, inferInstance, inferInstance, inferInstance, C, spMap (g.comp f₁) ≫ a,
    ⟨⟨inferInstance, inferInstance, inferInstance, ‹_›⟩, ‹_›⟩, hcomp, hcl⟩

end GlobalTheory.UChartTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyOpenThetaRingRegularStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonempty_open_thetaRing_regular : ∀ X₁ : GlobalTheory.GSep.GSet, ∃ U : X₁.M.Z.Opens, (U : Set X₁.M.Z).Nonempty ∧ ∀ z ∈ U, X₁.S.R ≤ X₁.M.O z := by
  first | exact @GlobalTheory.GSep.exists_opens_R_le_O | exact GlobalTheory.GSep.exists_opens_R_le_O | (intros; apply GlobalTheory.GSep.exists_opens_R_le_O <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedBlowup_finite_normal_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)), IsCov C g z₁ ζ → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (sM : M ⟶ Sp ℤ) (U₁ : S₁.Opens), LocallyOfFiniteType sM ∧ QuasiCompact sM ∧ Flat (p₁ ≫ sM) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) ∧ (U₁ : Set S₁).Nonempty ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S₁) (ev : M.presheaf.stalk z₁ →+* K), x ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → Set.range x ⊆ (U₁ : Set S₁) → ∃ y : Sp K ⟶ Xo.XF c, y ≫ C.iF = spMap ev ≫ ζ) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (ev : M.presheaf.stalk z₁ →+* R), a ≫ π = spMap ev ≫ ζ → Set.range (jK R ≫ a ≫ π) ⊆ Set.range C.iF → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (ev' : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev' ≫ a) p = a (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ a) → (∀ p, (spMap ev' ≫ ξ₁) p = ξ₁ (closedPoint R)) ∧ GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ ξ₁) := by
  first | exact @GlobalTheory.USepCov.exists_cover | exact GlobalTheory.USepCov.exists_cover | (intros; apply GlobalTheory.USepCov.exists_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapFixingDescendedPointsSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_objMap_fixing_descended_points_subfield : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Bb : Type} [CommRing Bb] {b : Base l Bb} (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ {s : Sp K ⟶ Sp Bb} (o : Obj D l b s) (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (π : o.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback o.t.G B₀ (spMap k₀.subtype) π → LBIso o.t.PP.L (M₀.pull π) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∃ n : ObjMap o o (spMap (σ : K →+* K)), ∀ x : Sp K ⟶ o.t.G.left, x ≫ o.t.G.hom = 𝟙 _ → (∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀) → x ≫ n.toSABMap.φ = spMap (σ : K →+* K) ≫ x := by
  first | exact @GlobalTheory.AutLift.exists_objMap_fixing_descended_points | exact GlobalTheory.AutLift.exists_objMap_fixing_descended_points | (intros; apply GlobalTheory.AutLift.exists_objMap_fixing_descended_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeTransversalIsotropic
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.Transv

theorem fin_max : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite :=
  GlobalTheory.T.finite_maximal_ideals_containing_natCast'

theorem exists_sep : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 :=
  GlobalTheory.T.exists_one_mod_maximal_mem_other_maximals_over_nat

theorem sup_eq_top : ∀ {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (N : Submodule (𝓞 E) X) (n : ℕ) (hn : 0 < n)
    (h : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → N ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤),
    N ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) = ⊤ :=
  GlobalTheory.T.sup_smul_top_eq_top_of_forall_maximal_over_nat

theorem exists_ker_vec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 :=
  GlobalTheory.T.exists_vector_mapsInto_ideal_of_not_onto_mod

theorem exists_real_theta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E))
    (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) :=
  GlobalTheory.T.exists_conj_invariant_trace_generator_local

theorem img_bar_ne_top : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ :=
  GlobalTheory.T.isotropicImage_not_onto_mod_conj_ideal

theorem improves_A : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_orthogonal

theorem rankOneChange_improves_real_prime_first : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_rankOneChange_improves_image_real_prime

theorem rankOneChange_improves_nonreal_prime : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_ne_conj

theorem img_top_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hc : Cois D y n)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hZ : Z.map y ≤ img D y Z' 𝔭) (hL : ∀ m ∈ perp D Z ⊓ perp D Z', y m ∈ img D y Z' 𝔭) :
    img D y Z' 𝔭 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, e, hae⟩ := hc.1 x
  obtain ⟨z, hz, m, hm, b, hb, rfl⟩ := h.exists_decomp a
  have h1 : y (z + m + b) ∈ img D y Z' 𝔭 := by
    rw [map_add, map_add]
    exact add_mem (add_mem (hZ ⟨z, hz, rfl⟩) (hL m hm)) (Submodule.mem_sup_left ⟨b, hb, rfl⟩)
  have h2 : n • e ∈ img D y Z' 𝔭 := by
    apply Submodule.mem_sup_right
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hn𝔭 trivial
  have h3 : x = y (z + m + b) - n • e := by rw [hae]; abel
  rw [h3]
  exact sub_mem h1 h2

theorem improve {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) : ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  obtain ⟨e, he1, he⟩ := exists_sep (E := E) n hn 𝔭 h𝔭
  obtain ⟨v, hv, ℓ₀, hℓ₀⟩ := exists_ker_vec D y Z Z' h hr 𝔭 h𝔭 hi
  obtain ⟨θ, hθ, s, hs, hs', hgen⟩ := exists_real_theta H 𝔭 h𝔭
  by_cases hA : ∃ m ∈ perp D Z ⊓ perp D Z', y m ∉ img D y Z' 𝔭 ∧
      (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭)
  · obtain ⟨m, hm, hym, hA⟩ := hA
    exact improves_A D y n Z Z' h 𝔭 h𝔭 hn𝔭 e he1 he v hv ℓ₀ hℓ₀ m hm hym hA
  have hZ : ¬ Z.map y ≤ img D y Z' 𝔭 := fun hZ =>
    hi (img_top_of D y n hc Z Z' h 𝔭 hn𝔭 hZ fun m hm => by_contra fun h' => hA ⟨m, hm, h', Or.inr hZ⟩)
  by_cases hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭
  · exact rankOneChange_improves_real_prime_first D y n Z Z' h 𝔭 h𝔭 hb e he1 he v hv ℓ₀ hℓ₀ θ hθ s hs hs' hgen hZ
  have hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭 := by
    rintro _ ⟨m, hm, rfl⟩
    exact by_contra fun h' => hA ⟨m, hm, h', Or.inl hb⟩
  have hi' := img_bar_ne_top D y n hn hc Z Z' h hr 𝔭 h𝔭 hn𝔭 hi hL
  have h𝔭' : (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := Ideal.map_isMaximal_of_equiv H.bar
  have hn𝔭' : (n : 𝓞 E) ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn𝔭
  obtain ⟨e', he1', he'⟩ := exists_sep (E := E) n hn _ h𝔭'
  obtain ⟨v₂, hv₂, ℓ₁, hℓ₁⟩ := exists_ker_vec D y Z Z' h hr _ h𝔭' hi'
  exact rankOneChange_improves_nonreal_prime D y n Z Z' h 𝔭 h𝔭 hn𝔭 hb e he1 he e' he1' he' v hv ℓ₀ hℓ₀ v₂ hv₂ ℓ₁ hℓ₁ θ hθ s hs hs' hgen hZ

end GlobalTheory.LowFilt.Transv

namespace GlobalTheory.LowFilt

open GlobalTheory.LowFilt.Transv in
theorem exists_opp_transv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → Cois D y n → ∀ Z Z₀ : Submodule (𝓞 E) D.La, IsOpp D Z Z₀ →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' ∧ ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n hn hc Z Z₀ h0 hr
  classical
  let S := {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}
  haveI : Finite S := (fin_max (E := E) n hn).to_subtype
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  let F : Submodule (𝓞 E) D.La → (S → Submodule (𝓞 E) X) := fun Z' q => img D y Z' q.1
  haveI : IsNoetherian (𝓞 E) X := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) X
  have h1 : WellFoundedLT (S → (Submodule (𝓞 E) X)ᵒᵈ) := Pi.wellFoundedLT
  haveI : WellFoundedGT (S → Submodule (𝓞 E) X) := ⟨h1.wf⟩
  have wf : WellFounded (fun a b : S → Submodule (𝓞 E) X => b < a) := wellFounded_gt
  obtain ⟨_, ⟨Z', hZ', rfl⟩, hmax⟩ := wf.has_min (F '' {Z' | IsOpp D Z Z'}) ⟨_, Z₀, h0, rfl⟩
  have htop : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 →
      Z'.map y ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤ := by
    intro 𝔮 hq hnq
    by_contra hne
    obtain ⟨Z'', h1, h2, h3⟩ := improve D y n hn hc Z Z' hZ' hr 𝔮 hq hnq hne
    exact hmax (F Z'') ⟨Z'', h1, rfl⟩
      (lt_of_le_not_ge (fun q => h2 q.1 q.2.1 q.2.2) fun hle => h3 (hle ⟨𝔮, hq, hnq⟩))
  have hall := sup_eq_top (Z'.map y) n hn htop
  refine ⟨Z', hZ', fun x => ?_⟩
  have hx : x ∈ Z'.map y ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) := by rw [hall]; trivial
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_sup] at hx
  obtain ⟨_, ⟨b, hb, rfl⟩, w, hw, hsum⟩ := hx
  obtain ⟨e', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
  refine ⟨b, hb, -e', ?_⟩
  rw [smul_neg, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hsum]
  abel

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_points_frames_thetaSection_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  first | exact @GlobalTheory.GSep.exists_points_frames_theta | exact GlobalTheory.GSep.exists_points_frames_theta | (intros; apply GlobalTheory.GSep.exists_points_frames_theta <;> assumption)
end

