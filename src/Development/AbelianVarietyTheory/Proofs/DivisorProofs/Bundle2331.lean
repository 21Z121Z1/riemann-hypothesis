import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyFreeSubsheafDetIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SubGlue
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.LB (resG_resG resG_self exists_fun_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)

variable {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {L : LB X}

abbrev spanRes (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (k : L.ι) {W : X.Opens} (hk : W ≤ L.U k) :
    Submodule Γ(X, W) Γ(F, W) :=
  Submodule.span Γ(X, W) (Set.range fun i => resM F hk (s k i))

theorem resM_mem_spanRes (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) {k : L.ι} {W W' : X.Opens}
    (hW : W' ≤ W) (hk : W ≤ L.U k) {x : Γ(F, W)} (hx : x ∈ spanRes s k hk) :
    resM F hW x ∈ spanRes s k (hW.trans hk) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => resG X hW (c i), ?_⟩
  simp only [map_sum, resM_smul, resM_resM]

theorem spanRes_le (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k'))
    (hA : ∀ (k k' : L.ι) (i : Fin r), resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) =
      ∑ j, A k k' j i • resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j))
    (k k' : L.ι) {W : X.Opens} (hk : W ≤ L.U k) (hk' : W ≤ L.U k') :
    spanRes s k' hk' ≤ spanRes s k hk := by
  rw [spanRes, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have e := congrArg (resM F (le_inf hk hk')) (hA k k' i)
  simp only [resM_resM, map_sum, resM_smul] at e
  change resM F hk' (s k' i) ∈ spanRes s k hk
  rw [show resM F hk' (s k' i) = _ from e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

def IsLoc (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (V : X.Opens) (x : Γ(F, V)) : Prop :=
  ∀ p ∈ V, ∃ (k : L.ι) (W : X.Opens) (h : W ≤ V) (hk : W ≤ L.U k), p ∈ W ∧
    resM F h x ∈ spanRes s k hk

def sub (hL : L.IsLB) (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (hmono : ∀ (k k' : L.ι) (W : X.Opens) (hk : W ≤ L.U k) (hk' : W ≤ L.U k'),
      spanRes s k' hk' ≤ spanRes s k hk) : VB.Sub F where
  sec V :=
    { carrier := {x | IsLoc s V x}
      zero_mem' := fun p hp => by
        obtain ⟨k, hk⟩ := Semi.LB.mem_of_cover hL p
        exact ⟨k, V ⊓ L.U k, inf_le_left, inf_le_right, ⟨hp, hk⟩, by rw [map_zero]; exact zero_mem _⟩
      add_mem' := fun {x y} hx hy p hp => by
        obtain ⟨k, W, h, hk, hpW, hxW⟩ := hx p hp
        obtain ⟨k', W', h', hk', hpW', hyW'⟩ := hy p hp
        refine ⟨k, W ⊓ W', inf_le_left.trans h, inf_le_left.trans hk, ⟨hpW, hpW'⟩, ?_⟩
        rw [map_add]
        refine add_mem ?_ (hmono k k' _ (inf_le_left.trans hk) (inf_le_right.trans hk') ?_)
        · have := resM_mem_spanRes s (inf_le_left : W ⊓ W' ≤ W) hk hxW
          rw [resM_resM] at this
          exact this
        · have := resM_mem_spanRes s (inf_le_right : W ⊓ W' ≤ W') hk' hyW'
          rw [resM_resM] at this
          exact this
      smul_mem' := fun a x hx p hp => by
        obtain ⟨k, W, h, hk, hpW, hxW⟩ := hx p hp
        refine ⟨k, W, h, hk, hpW, ?_⟩
        rw [resM_smul]
        exact Submodule.smul_mem _ _ hxW }
  res_mem {V W} hWV x hx := fun p hp => by
    obtain ⟨k, W', h', hk, hp', hx'⟩ := (hx : IsLoc s V x) p (hWV hp)
    refine ⟨k, W ⊓ W', inf_le_left, inf_le_right.trans hk, ⟨hp, hp'⟩, ?_⟩
    rw [resM_resM]
    have := resM_mem_spanRes s (inf_le_right : W ⊓ W' ≤ W') hk hx'
    rw [resM_resM] at this
    exact this
  mem_of_local {V x} H := fun p hp => by
    obtain ⟨W, h, hpW, hW⟩ := H p hp
    obtain ⟨k, W', h', hk, hp', hx'⟩ := (hW : IsLoc s W _) p hpW
    refine ⟨k, W', h'.trans h, hk, hp', ?_⟩
    rw [resM_resM] at hx'
    exact hx'

theorem mem_spanRes_of_mem (hL : L.IsLB) (s : ∀ k : L.ι, Fin r → Γ(F, L.U k))
    (hmono : ∀ (k k' : L.ι) (W : X.Opens) (hk : W ≤ L.U k) (hk' : W ≤ L.U k'),
      spanRes s k' hk' ≤ spanRes s k hk)
    (hli : ∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k),
      LinearIndependent Γ(X, V) fun i => resM F h (s k i))
    {k : L.ι} {V : X.Opens} (hV : V ≤ L.U k) {x : Γ(F, V)}
    (hx : x ∈ (sub hL s hmono).sec V) : x ∈ spanRes s k hV := by
  have hx' : IsLoc s V x := hx
  choose k' W hW hk' hpW hxW using fun p : V => hx' p p.2
  have hc : V ≤ iSup W := fun p hp => Opens.mem_iSup.2 ⟨⟨p, hp⟩, hpW _⟩
  have hin (p : V) : resM F (hW p) x ∈ spanRes s k ((hW p).trans hV) :=
    hmono k (k' p) _ _ _ (hxW p)
  choose c hc' using fun p => (Submodule.mem_span_range_iff_exists_fun _).1 (hin p)
  have key (p q : V) (i : Fin r) : resG X (inf_le_left : W p ⊓ W q ≤ W p) (c p i) =
      resG X (inf_le_right : W p ⊓ W q ≤ W q) (c q i) := by
    have hl := hli k (W p ⊓ W q) (inf_le_left.trans ((hW p).trans hV))
    have e1 := congrArg (resM F (inf_le_left : W p ⊓ W q ≤ W p)) (hc' p)
    have e2 := congrArg (resM F (inf_le_right : W p ⊓ W q ≤ W q)) (hc' q)
    simp only [map_sum, resM_smul, resM_resM] at e1 e2
    exact Fintype.linearIndependent_iffₛ.1 hl _ _ (e1.trans e2.symm) i
  choose b hb using fun i => exists_fun_of_cover W hW hc (fun p => c p i) fun p q => key p q i
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨b, ?_⟩
  refine sec_ext_of_cover W hW hc fun p => ?_
  simp only [map_sum, resM_smul, resM_resM, hb]
  exact hc' p

end GlobalTheory.SubGlue

namespace GlobalTheory.SubGlue
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.QCoh (appLinear appLinear_apply)

theorem exists_sub_isVB_lbIso_det : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (L : LB X), L.IsLB → ∀ (s : ∀ k : L.ι, Fin r → Γ(F, L.U k)) (A : ∀ k k' : L.ι, Matrix (Fin r) (Fin r) Γ(X, L.U k ⊓ L.U k')), (∀ (k : L.ι) (V : X.Opens) (h : V ≤ L.U k), LinearIndependent Γ(X, V) fun i => GlobalTheory.Twist.resM F h (s k i)) → (∀ (k k' : L.ι) (i : Fin r), GlobalTheory.Twist.resM F (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (s k' i) = ∑ j, A k k' j i • GlobalTheory.Twist.resM F (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k) (s k j)) → (∀ k k' : L.ι, (L.g k k').val = (A k k').det) → ∃ (W : X.Modules) (ι : W ⟶ F), Mono ι ∧ GlobalTheory.VB.IsVB W r ∧ LBIso L (GlobalTheory.VB.det W r) := by
  intro X F r L hL s A hli hA hdet
  have hmono := spanRes_le s A hA
  let N := sub hL s hmono
  have hmem (k : L.ι) (i : Fin r) : s k i ∈ N.sec (L.U k) := fun p hp =>
    ⟨k, L.U k, le_rfl, le_rfl, hp, Submodule.subset_span ⟨i, rfl⟩⟩
  have hfr (k : L.ι) : VB.IsFrame fun i => N.mkSec (s k i) (hmem k i) :=
    GlobalTheory.EigenFrames.isFrame_mkSec N (s k) (hmem k) (hli k)
      fun V h x hx => mem_spanRes_of_mem hL s hmono hli h hx
  have hv (k k' : L.ι) (i : Fin r) :
      resM N.toMod (inf_le_right : L.U k ⊓ L.U k' ≤ L.U k') (N.mkSec (s k' i) (hmem k' i)) =
        ((hfr k).basis (inf_le_left : L.U k ⊓ L.U k' ≤ L.U k)).equivFun.symm
          fun j => A k k' j i := by
    rw [VB.IsFrame.basis_equivFun_symm]
    apply N.incl_app_injective
    rw [app_resM, VB.Sub.incl_app_mkSec, hA]
    rw [← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, appLinear_apply, app_resM, VB.Sub.incl_app_mkSec]
  refine ⟨N.toMod, N.incl, inferInstance, ?_⟩
  refine VB.lbIso_det_of_frames hL _ hfr fun k k' => Units.ext ?_
  rw [hdet, VB.IsFrame.val_detUnit, Module.Basis.det_apply]
  congr 1
  ext a b
  rw [Module.Basis.toMatrix_apply, hv, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.SubGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogDerLoc

def dualHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (D : Derivation ℤ A A) :
    A →+* TrivSqZeroExt B B where
  toFun r := TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [D.leibniz, mul_comm, -DualNumber.inr_eq_smul_eps]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [-DualNumber.inr_eq_smul_eps]

theorem exists_extension {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (f : A) [IsLocalization.Away f B]
    (D : Derivation ℤ A A) : ∃ E : Derivation ℤ B B, ∀ r, E (algebraMap A B r) = algebraMap A B (D r) := by
  have hu : IsUnit (dualHom (algebraMap A B) D f) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
      simpa [dualHom] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let L : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hfst : ∀ x, (L x).fst = x := fun x => by
    have : (TrivSqZeroExt.fstHom B _ _).toRingHom.comp L = RingHom.id _ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [L, dualHom]
    exact congr($this x)
  let e : B →+ B :=
    { toFun := fun x => (L x).snd
      map_zero' := by rw [map_zero, TrivSqZeroExt.snd_zero]
      map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add] }
  refine ⟨Derivation.mk' e.toIntLinearMap fun x y => ?_, fun r => ?_⟩
  · change (L (x * y)).snd = x • (L y).snd + y • (L x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · change (L (algebraMap A B r)).snd = _
    simp [L, dualHom, -DualNumber.inr_eq_smul_eps]

theorem map_mem_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (D : Derivation ℤ A A)
    (E : Derivation ℤ B B) (h : ∀ r, E (φ r) = φ (D r)) (J : Ideal A) (hJ : ∀ g ∈ J, D g ∈ J) :
    ∀ x ∈ J.map φ, E x ∈ J.map φ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [h]
    exact Ideal.mem_map_of_mem φ (hJ g hg)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx hE =>
    rw [smul_eq_mul, E.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ a hE) (Ideal.mul_mem_right _ _ hx)

theorem exists_logDer_basicOpen : ∀ (X : Scheme.{0}) (K : Type) [CommRing K] (s : X ⟶ Sp K) (I : X.IdealSheafData) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ Dl ∈ GlobalTheory.LogKS.logDer s I U, ∃ DlW ∈ GlobalTheory.LogKS.logDer s I W, ∀ r, DlW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := by
  intro X K _ s I U W hW f hf Dl hD
  obtain rfl : W = X.affineBasicOpen f := Subtype.ext hf
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  obtain ⟨E, hE⟩ := exists_extension (B := Γ(X, X.basicOpen f)) f Dl
  have hE' : ∀ r, E ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := hE
  refine ⟨E, ⟨fun a => ?_, ?_⟩, hE'⟩
  · have hc : (X.presheaf.map (homOfLE hW).op).hom (constFn s U.1 a) = constFn s (X.affineBasicOpen f).1 a := by
      exact congr(($(Scheme.Hom.appLE_map s (U := ⊤) (V := U.1) (fun _ _ => trivial) (homOfLE hW).op)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    have := hE' (constFn s U.1 a)
    rw [hc, hD.1 a, map_zero] at this
    exact this
  · rw [← I.map_ideal_basicOpen U f]
    exact map_mem_map _ Dl E hE' _ hD.2

end GlobalTheory.LogDerLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalMvPolynomialLocalization
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.DedekindDimFormula
open ReciprocityTheory.CA

theorem isMaximal_comap_C {o : Type} [CommRing o] [IsJacobsonRing o] (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o)).IsMaximal := by
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) o ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

theorem isCM_localization (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] :
    ∃ δ : ℕ, ∀ (p : Ideal o) [p.IsMaximal],
      IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = δ := by
  by_cases hf : IsField o
  · refine ⟨0, fun p _ => ?_⟩
    letI := hf.toField
    have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsMaximal.ne_top inferInstance)
    have hd : ringKrullDim (Localization.AtPrime p) = 0 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp,
        Ideal.height_bot]
      rfl
    refine ⟨⟨inferInstance, 0, by rw [hd]; rfl, ?_⟩, hd⟩
    refine ⟨[], rfl, by simp, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simp)]
    exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  · refine ⟨1, fun p _ => ?_⟩
    have hp : p ≠ ⊥ := by
      intro h
      exact hf (Ring.isField_iff_maximal_bot.mpr (h ▸ inferInstance))
    haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o hp _
    have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
    refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, by rw [hd]; rfl⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
    refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
      RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact IsSMulRegular.of_ne_zero hϖ.ne_zero

theorem exists_maximal_mvPolynomial_localization' {o : Type} [CommRing o] (N : ℕ) (p : Ideal o) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) o) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) o)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) o) ∈ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_comap W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap o (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

theorem polyEquidim : ∀ (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o] (N : ℕ),
    ∃ d : ℕ, ∀ (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal],
      IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = (d : ℕ∞) := by
  intro o _ _ _ _ N
  obtain ⟨δ, hδ⟩ := isCM_localization o
  refine ⟨δ + N, fun 𝔑 _ => ?_⟩
  haveI := isMaximal_comap_C N 𝔑
  obtain ⟨hCM, hdim⟩ := hδ (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization' N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((δ + N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

theorem affine_heights (o A : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o]
    [CommRing A] [IsDomain A] [Algebra o A] [Algebra.FiniteType o A] :
    ∃ h : ℕ, (∀ (M : Ideal A) [M.IsMaximal], M.height = (h : ℕ∞)) ∧
      ∀ (P M : Ideal A) [P.IsPrime] [M.IsMaximal],
        (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType o A›
  obtain ⟨d, hd⟩ := polyEquidim o N
  set Q := RingHom.ker (f : MvPolynomial (Fin N) o →+* A) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) o ⧸ Q) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) o →+* A)) hf
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (MvPolynomial (Fin N) o ⧸ Q)
  haveI : (M₀.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hQle : Q.height ≤ d := by
    rw [← (hd (M₀.comap (Ideal.Quotient.mk Q))).2]
    exact Ideal.height_mono fun x hx => by
      simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M₀.zero_mem]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Q.height = k := by
    have : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
    exact ⟨Q.height.toNat, (ENat.coe_toNat this).symm⟩
  have hkd : k ≤ d := by rw [hk] at hQle; exact_mod_cast hQle
  refine ⟨d - k, fun M _ => ?_, fun P M _ _ => ?_⟩
  · haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    haveI : ((M.comap e).comap (Ideal.Quotient.mk Q)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨hCM, hh⟩ := hd ((M.comap e).comap (Ideal.Quotient.mk Q))
    have e1 := GlobalTheory.FinTypeIntCatenary.height_comap_mk Q (M.comap e) hCM
    rw [hh, hk, RingEquiv.height_comap] at e1
    have : ((d - k : ℕ) : ℕ∞) + k = M.height + k := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hkd, e1, add_comm]
    exact (WithTop.add_right_cancel (ENat.coe_ne_top k) this).symm
  · haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
    haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    have h := GlobalTheory.FinTypeIntCatenary.height_le_of_equidim d (fun 𝔑 _ => hd 𝔑) Q (P.comap e) (M.comap e)
    rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
    have hdim : ringKrullDim ((MvPolynomial (Fin N) o ⧸ Q) ⧸ P.comap e) = ringKrullDim (A ⧸ P) :=
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
        (Ideal.map_comap_of_surjective _ e.surjective P).symm)
    rwa [hdim] at h

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

end GlobalTheory.DedekindDimFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAdding
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep.Centre

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem centreAt_of_dominatesStalk {E : DivOver p} {z : X} (h : DominatesStalk E.ring z) :
    CentreAt E z := by
  refine ⟨by rintro _ ⟨a, rfl⟩; exact h.1 a, ?_⟩
  rintro f ⟨a, ha⟩ h0
  have hinv : ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring :=
    (E.ord_nonneg_iff f⁻¹).1 (by rw [E.ord_inv, h0]; simp)
  have hu : IsUnit a := by
    by_contra hu
    have h1 := (E.ring.coe_mem_nonunits_iff (a := ⟨_, h.1 a⟩)).mp (h.2 a hu)
    refine h1 (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    change algebraMap _ X.functionField a * _ = 1
    rw [ha]
    exact f.mul_inv
  obtain ⟨u, rfl⟩ := hu
  refine ⟨((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), ?_⟩
  have e : algebraMap _ X.functionField
      ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * (f : X.functionField) = 1 := by
    rw [← ha, ← map_mul, Units.inv_mul, map_one]
  exact (Units.inv_eq_of_mul_eq_one_left e).symm

theorem exists_centreAt {E : DivOver p} {x : X} (h : E.Through x) :
    ∃ z, z ⤳ x ∧ CentreAt E z :=
  have ⟨z, hz, hd⟩ := exists_specializes_dominatesStalk_of_regAt X E.ring x h
  ⟨z, hz, centreAt_of_dominatesStalk hd⟩

theorem exists_isLogEqn_add [IsLocallyNoetherian X] {n : ℕ} {Δ D : X → ℚ} {η : RatForms p n}
    {x : X} {m : ℕ} {g : X.functionFieldˣ} (hD : IsQCart D) (hm : 0 < m)
    (hg : IsLogEqn p Δ η x m g) :
    ∃ (m' : ℕ) (g' : X.functionFieldˣ), 0 < m' ∧ IsLogEqn p (Δ + D) η x m' g' := by
  obtain ⟨r, D₀, hr, -, rfl⟩ := hD
  obtain ⟨d, hd⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hdV⟩ := hd.exists_nhds
  refine ⟨m * r, g ^ r * d ^ m, Nat.mul_pos hm hr, fun z hz E hE => ?_⟩
  have h1 := (hdV z (hz.mem_open V.isOpen hV)).mult_eq
  rw [← hE.ord_eq] at h1
  have h2 := hg z hz E hE
  have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [E.ord_mul, E.ord_pow, E.ord_pow, Pi.add_apply, qWeil, h1]
  push_cast
  rw [← h2]
  field_simp
  ring

theorem exists_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ KltAt p n (Δ + D) x →
    ∃ z, z ⤳ x ∧ IsNkltCentre p n (Δ + D) z := by
  intro X _ _ _ p n hp hn Δ D x hD hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨η, m, g, hη, hm, hg, -⟩ := hk
  obtain ⟨m', g', hm', hg'⟩ := exists_isLogEqn_add hD hm hg
  rw [hg'.kltAt_iff hn hη hm'] at hnk
  push_neg at hnk
  obtain ⟨E, hE, hd⟩ := hnk
  obtain ⟨z, hz, hc⟩ := exists_centreAt hE
  exact ⟨z, hz, E, η, m', g', hη, hm', fun w hw => hg' w (hw.trans hz), hc, hd⟩

end GlobalTheory.PairStep.Centre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrdersStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_etalePullback_orders : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z → ∃ E : DivOver p, E.IsAt (f z) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  first | exact @GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd | exact GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd | (intros; apply GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingSectionOfIsolatedNonKltPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separatingSection_of_isolatedNonKltPoint : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (ρ d : ℚ) (x x' : X), M.IsLB → IsEffQDiv Δ → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → QNum p N d D → d < ρ → IsClosed ({x} : Set X) → x ≠ x' → LcCut p n (Δ + D) x 0 → ¬ KltAt p n (Δ + D) x' → ∃ s : M.Sec, x ∈ nonzeroLocus s ∧ x' ∉ nonzeroLocus s := by
  first | exact @GlobalTheory.PairStep.exists_sec_sep_of_lcCut | exact GlobalTheory.PairStep.exists_sec_sep_of_lcCut | (intros; apply GlobalTheory.PairStep.exists_sec_sep_of_lcCut <;> assumption)
end

