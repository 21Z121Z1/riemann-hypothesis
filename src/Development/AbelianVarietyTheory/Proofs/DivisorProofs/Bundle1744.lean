import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetPowSectionRationalGenericPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.SecRat

theorem isIntegral_of_isGenOver (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C) (hx : IsGenOver k x) : IsIntegral C := by
  have : SmoothOfRelativeDimension 1 (strHom k C) := hx.1.1
  have : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  have hred : IsReduced C := isReduced_of_smooth_of_isReduced (strHom k C)
  have hd : IsDominant x := hx.2.1.1
  have hden : DenseRange x.base := hd.denseRange
  have hcl : closure {x.base default} = (Set.univ : Set C) := by
    have hr : Set.range x.base = {x.base default} := by
      ext y; constructor
      · rintro ⟨p, rfl⟩; rw [Subsingleton.elim p default]; rfl
      · rintro rfl; exact ⟨_, rfl⟩
    rw [← hr]; exact hden.closure_range
  have hirr : IsIrreducible (Set.univ : Set C) := hcl ▸ isIrreducible_singleton.closure
  have : IrreducibleSpace C := { isPreirreducible_univ := hirr.2, toNonempty := ⟨x.base default⟩ }
  exact (isIntegral_iff_irreducibleSpace_and_isReduced C).2 ⟨this, hred⟩

theorem not_isUnit_evAt {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (b : Sp R ⟶ X)
    {U : X.Opens} (h : ⊤ ≤ b ⁻¹ᵁ U) (f : Γ(X, U)) (hf : b (IsLocalRing.closedPoint R) ∉ X.basicOpen f) :
    ¬ IsUnit (evAt b h f) := by
  intro hu
  apply hf
  have h1 : (b.appLE U ⊤ h).hom f = (Scheme.ΓSpecIso (.of R)).inv.hom (evAt b h f) := by
    simp [evAt]
  have h2 : (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) = ⊤ ⊓ (Sp R).basicOpen ((b.app U).hom f) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
  have h3 : IsLocalRing.closedPoint R ∈ (Sp R).basicOpen ((b.appLE U ⊤ h).hom f) := by
    rw [h1, basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hu
  rw [h2, ← Scheme.preimage_basicOpen] at h3
  exact h3.2

theorem evAt_coord {R : Type} [CommRing R] {C : Scheme.{0}} (x : Sp R ⟶ C) {W : C.Modules} {r m : ℕ}
    (σ : (lbPow (det W r) m).Sec) (c₀ c : Chart W r) (V' : C.Opens) (h₀ : V' ≤ c₀.U) (h₁ : V' ≤ c.U)
    (hx' : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V'))
    (hM : ∀ j, resM W h₀ (c₀.e j) = ∑ i, M i j • resM W h₁ (c.e i))
    (h0 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c₀)) (h1 : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c)) :
    evAt x h1 (σ.f (fun _ => c)) = (M.map (evAt x hx')).det ^ m * evAt x h0 (σ.f (fun _ => c₀)) := by
  have hV : V' ≤ (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => h₁ hy, Set.mem_iInter.2 fun _ => h₀ hy⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ ((lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀)) :=
    hx'.trans (x.preimage_mono hV)
  have hcc : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c₀.U) := hx'.trans (x.preimage_mono (le_inf h₁ h₀))
  have e := congrArg (evAt x hxV) (σ.compat (fun _ => c) (fun _ => c₀))
  rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ _ h1 hxV, map_mul, (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ _ h0 hxV] at e
  rw [e]
  congr 1
  have hd : evAt x hcc (c.isFrame.detUnit c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right).val =
      (M.map (evAt x hx')).det := by
    rw [← (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ (le_inf h₁ h₀) hcc hx']
    have hr := IsFrame.res_detUnit c.isFrame c₀.isFrame (inf_le_left : c.U ⊓ c₀.U ≤ c.U) inf_le_right (le_inf h₁ h₀)
    refine (congrArg (evAt x hx') (congrArg Units.val hr)).trans ?_
    rw [IsFrame.val_detUnit, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, hM]
    simp only [← IsFrame.basis_apply c.isFrame h₁]
    rw [Module.Basis.repr_sum_self]
  rw [← hd, ← map_pow, ← (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 R C x _ _ (fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (lbPow (det W r) m).U (fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) ≤ c.U ⊓ c₀.U) hcc hxV]
  congr 1
  dsimp only [lbPow, LB.LinComb]
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val]
  erw [map_pow]
  congr 1

theorem val_lt_one {k K : Type} [Field k] [Field K] [Algebra k K] (v : Place k K) (a : v.O) (ha : ¬ IsUnit a) :
    v.1 (a : K) < 1 := by
  have h1 : v.1 (a : K) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 a.2
  refine lt_of_le_of_ne h1 fun h => ha ?_
  have h0 : (a : K) ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hi : (a : K)⁻¹ ∈ v.O := (Valuation.mem_valuationSubring_iff _ _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem sec_eq_zero {X : Scheme.{0}} {L : LB X} (σ : L.Sec) (h : ∀ j, σ.f j = 0) : σ = 0 := by
  obtain ⟨f, hc⟩ := σ
  have : f = fun _ => 0 := funext h
  subst this
  rfl

end GlobalTheory.Nef.SecRat

open GlobalTheory.Nef.SecRat in

theorem GlobalTheory.Nef.sec_detPow_rational : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ (m : ℕ) (σ : (lbPow (det W r) m).Sec), σ ≠ 0 → ∃ f : K, f ≠ 0 ∧ ∀ (v : Place k K) (g : Matrix (Fin r) (Fin r) K), LocFrame x s v g → v.1 (f * g.det ^ m) ≤ 1 ∧ ∀ b : Sp v.O ⟶ C, spMap v.O.subtype ≫ b = x → b (IsLocalRing.closedPoint v.O) ∉ Out.nonzeroLocus σ → v.1 (f * g.det ^ m) < 1 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s hV₀ hs m σ hσ
  haveI := isIntegral_of_isGenOver k K C x hx
  let c₀ : Chart W r := ⟨V₀, s, hs⟩
  have hUeq : ∀ c : Chart W r, (((lbPow (det W r) m).U (fun _ => c) : C.Opens) : Set C) = c.U := fun c =>
    Set.ext fun y => ⟨fun hy => Set.mem_iInter.1 hy PUnit.unit, fun hy => Set.mem_iInter.2 fun _ => hy⟩
  have hle : ∀ c : Chart W r, c.U ≤ (lbPow (det W r) m).U (fun _ => c) := fun c y hy =>
    Set.mem_iInter.2 fun _ => hy
  obtain ⟨hx0, hinj0, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 ((lbPow (det W r) m).U fun _ => c₀)
    (by rw [hUeq]; exact hV₀)
  refine ⟨evAt x hx0 (σ.f fun _ => c₀), ?_, ?_⟩
  · intro hf
    apply hσ
    have h0 : σ.f (fun _ => c₀) = 0 := hinj0 (by rw [hf, map_zero])
    refine sec_eq_zero σ fun j => ?_
    have hj : j = fun _ => j PUnit.unit := funext fun _ => rfl
    rw [hj]
    generalize j PUnit.unit = c
    by_cases hne : (((lbPow (det W r) m).U fun _ => c : C.Opens) : Set C).Nonempty
    · have hne2 : ((((lbPow (det W r) m).U fun _ => c) ⊓ (lbPow (det W r) m).U (fun _ => c₀) :
          C.Opens) : Set C).Nonempty :=
        nonempty_preirreducible_inter (Opens.isOpen _) (Opens.isOpen _) hne (by rw [hUeq]; exact hV₀)
      obtain ⟨hxj, hinjj, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 _ hne
      obtain ⟨hx2, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 _ hne2
      apply hinjj
      have e := congrArg (evAt x hx2) (σ.compat (fun _ => c) (fun _ => c₀))
      rw [(GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 K C x _ _ _ hxj hx2, map_mul, (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).2.2.1 K C x _ _ _ hx0 hx2, h0,
        map_zero, mul_zero] at e
      rw [e, map_zero]
    · exact eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => hne ⟨y, C.basicOpen_le _ hy⟩)
  · rintro v g ⟨b, V, t, V', h₀, h₁, hx', M, hb, hbV, ht, hM, rfl⟩
    let c : Chart W r := ⟨V, t, ht⟩
    have hbj : ⊤ ≤ b ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hbV.trans (b.preimage_mono (hle c))
    have hxj : ⊤ ≤ x ⁻¹ᵁ (lbPow (det W r) m).U (fun _ => c) := hx'.trans (x.preimage_mono (h₁.trans (hle c)))
    have key := evAt_coord x σ c₀ c V' h₀ h₁ hx' M hM hx0 hxj
    have hval : v.1 (evAt x hx0 (σ.f fun _ => c₀) * (M.map (evAt x hx')).det ^ m) =
        v.1 ((evAt b hbj (σ.f fun _ => c) : v.O) : K) := by
      rw [mul_comm, ← key]
      congr 1
      subst hb
      exact (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk).1 v.O K C v.O.subtype b _ hbj hxj _
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact (Valuation.mem_valuationSubring_iff _ _).1 (evAt b hbj _).2
    · intro b' hb' hout
      have e : spMap (algebraMap K K) ≫ x = x := by
        rw [Algebra.algebraMap_self, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      obtain ⟨b₀, -, huniq⟩ := GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve k K K C x hx v
      have hbb : b' = b := (huniq b' (hb'.trans e.symm)).trans (huniq b (hb.trans e.symm)).symm
      subst hbb
      have hnu := not_isUnit_evAt b' hbj (σ.f fun _ => c) (fun hm => hout (Opens.mem_iSup.2 ⟨_, hm⟩))
      rw [hval]
      exact val_lt_one v _ hnu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetValuationsSumZeroSameLocalLattice
section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.TwoBasesDet

theorem exists_leftInv {K : Type} [Field K] {n g : ℕ} (b : Fin n → Fin g → K)
    (hb : LinearIndependent K b) :
    ∃ A : Matrix (Fin n) (Fin g) K, ∀ i j, ∑ k, A i k * b j k = if i = j then 1 else 0 := by
  let lc : (Fin n → K) →ₗ[K] (Fin g → K) := Fintype.linearCombination K b
  have hinj : LinearMap.ker lc = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact funext (Fintype.linearIndependent_iff.1 hb c (by simpa [lc, Fintype.linearCombination_apply] using hc))
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective lc hinj
  refine ⟨LinearMap.toMatrix' f, fun i j => ?_⟩
  have h1 : f (b j) = Pi.single j 1 := by
    have : lc (Pi.single j 1) = b j := by simp [lc, Fintype.linearCombination_apply_single]
    rw [← this, ← LinearMap.comp_apply, hf, LinearMap.id_apply]
  have h3 : (Matrix.mulVec (LinearMap.toMatrix' f) (b j)) = f (b j) := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have h2 := congrFun (h3.trans h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem vV_algebraMap_unit (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] {u : V} (hu : IsUnit u) :
    vV V (algebraMap V K' u) = 0 := by
  unfold vV valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2]
  · simp
  · exact fun h => (HeightOneSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem valuation_div_le_one {K : Type} [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K))
    (c d : 𝓞 K) (hd : d ∉ 𝔓.asIdeal) : 𝔓.valuation K ((c : K) / d) ≤ 1 := by
  rw [map_div₀]
  have h1 : 𝔓.valuation K (d : K) = 1 := by
    rw [show (d : K) = algebraMap (𝓞 K) K d from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hd
  rw [h1, div_one, show (c : K) = algebraMap (𝓞 K) K c from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem det_vV_add_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (g n : ℕ) (L : Submodule (𝓞 K) (Fin g → K)) (b : Fin n → Fin g → K), GlobalTheory.PtDeg.LocBasis 𝔓 L b → ∀ (M : Matrix (Fin n) (Fin n) K) (u : Fin n → Fin g → K), (∀ i, u i = ∑ j, M i j • b j) → ∀ (C : Matrix (Fin n) (Fin n) T.Fr), (∀ i, (∑ j, C i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K)))) → (∀ v ∈ L, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C i j • fun k => iK (u j k))) → M.det ≠ 0 ∧ C.det ≠ 0 ∧ vV T.V C.det + vV T.V (iK M.det) = 0 := by
  intro K _ _ 𝔓 T iK hiK g n L b hb M u hu C hW hL
  set B : Fin n → Fin g → T.Fr := fun l k => iK (b l k) with hBdef
  obtain ⟨A, hA⟩ := exists_leftInv b hb.2.1

  have key : ∀ z : Fin n → T.Fr, ∀ i, z i = ∑ k, iK (A i k) * ∑ l, z l * B l k := by
    intro z i
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ k, iK (A i k) * (z l * B l k) = if i = l then z l else 0 := by
      intro l
      have h := congrArg iK (hA i l)
      rw [map_sum] at h
      simp only [map_mul] at h
      calc ∑ k, iK (A i k) * (z l * B l k) = z l * ∑ k, iK (A i k) * iK (b l k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by simp only [hBdef]; ring
        _ = _ := by rw [h]; split_ifs <;> simp
    simp_rw [h]; simp
  have hinj : ∀ x y : Fin n → T.Fr, (∀ k, ∑ l, x l * B l k = ∑ l, y l * B l k) → x = y := by
    intro x y hxy
    funext i
    rw [key x i, key y i]
    exact Finset.sum_congr rfl fun k _ => by rw [hxy k]

  set P : Matrix (Fin n) (Fin n) T.Fr := C * M.map iK with hPdef
  have hWP : ∀ i k, (∑ j, C i j • fun k => iK (u j k)) k = ∑ l, P i l * B l k := by
    intro i k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hu, map_sum, map_mul, hPdef, Matrix.mul_apply,
      Matrix.map_apply, hBdef, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

  have hint : ∀ x ∈ L, ∃ p : Fin n → T.V, ∀ k, iK (x k) = ∑ l, algebraMap T.V T.Fr (p l) * B l k := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hb.2.2 x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hdx
    have hd0 : (d : K) ≠ 0 := by
      intro h0
      apply hd
      have : d = 0 := by exact_mod_cast h0
      rw [this]; exact Submodule.zero_mem _
    choose p hp using fun l => (hiK ((c l : K) / d)).2 (valuation_div_le_one 𝔓 (c l) d hd)
    refine ⟨p, fun k => ?_⟩
    have hk := congrFun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at hk
    have hx' : x k = ∑ l, ((c l : K) / d) * b l k := by
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
      rw [eq_div_iff hd0]
      convert hk.symm using 1
      · ring
    simp only [hp, hBdef, hx', map_sum, map_mul]
  have hspan : ∀ w ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K))),
      ∃ p : Fin n → T.V, ∀ k, w k = ∑ l, algebraMap T.V T.Fr (p l) * B l k := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      exact hint x hx
    | zero => exact ⟨0, fun k => by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨p, hp⟩ := h
      obtain ⟨p', hp'⟩ := h'
      exact ⟨p + p', fun k => by simp [hp, hp', add_mul, Finset.sum_add_distrib]⟩
    | smul a w _ h =>
      obtain ⟨p, hp⟩ := h
      refine ⟨a • p, fun k => ?_⟩
      simp only [Pi.smul_apply, Algebra.smul_def, hp, Finset.mul_sum, smul_eq_mul, map_mul, mul_assoc]
      exact Finset.sum_congr rfl fun _ _ => by simp only [Algebra.algebraMap_self, RingHom.id_apply]

  have hPint : ∀ i, ∃ p : Fin n → T.V, ∀ l, P i l = algebraMap T.V T.Fr (p l) := by
    intro i
    obtain ⟨p, hp⟩ := hspan _ (hW i)
    refine ⟨p, fun l => congrFun (hinj (P i) (fun l => algebraMap T.V T.Fr (p l)) fun k => ?_) l⟩
    rw [← hWP, hp]
  choose Pv hPv using hPint
  have hPeq : P = (Matrix.of Pv).map (algebraMap T.V T.Fr) := by
    ext i l; simp [hPv i l]

  have hQint : ∀ l, ∃ q : Fin n → T.V, ∀ m, ∑ i, algebraMap T.V T.Fr (q i) * P i m = if l = m then 1 else 0 := by
    intro l
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hL (b l) (hb.1 l))
    refine ⟨q, fun m => congrFun (hinj (fun m => ∑ i, algebraMap T.V T.Fr (q i) * P i m)
      (fun m => if l = m then 1 else 0) fun k => ?_) m⟩
    have hk : ∑ i, algebraMap T.V T.Fr (q i) * (∑ j, C i j • fun k => iK (u j k)) k = iK (b l k) := by
      rw [← congrFun hq k, Finset.sum_apply]
      simp only [Pi.smul_apply, Algebra.smul_def]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ m, algebraMap T.V T.Fr (q i) * P i m * B m k
        = ∑ i, algebraMap T.V T.Fr (q i) * (∑ j, C i j • fun k => iK (u j k)) k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hWP, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = B l k := hk
  choose Qv hQv using hQint
  have hQP : Matrix.of Qv * Matrix.of Pv = 1 := by
    apply (Matrix.map_injective (IsFractionRing.injective T.V T.Fr))
    show (Matrix.of Qv * Matrix.of Pv).map (algebraMap T.V T.Fr) = (1 : Matrix (Fin n) (Fin n) T.V).map (algebraMap T.V T.Fr)
    rw [Matrix.map_mul, ← hPeq, Matrix.map_one _ (map_zero _) (map_one _)]
    ext l m
    simpa [Matrix.mul_apply, Matrix.one_apply] using hQv l m
  have hunit : IsUnit (Matrix.of Pv).det := by
    have := congrArg Matrix.det hQP
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact ⟨⟨_, _, by rw [mul_comm]; exact this, this⟩, rfl⟩
  have hdetP : P.det = algebraMap T.V T.Fr (Matrix.of Pv).det := by
    rw [hPeq, RingHom.map_det]; rfl
  have hdetP' : P.det = C.det * iK M.det := by
    rw [hPdef, Matrix.det_mul, RingHom.map_det]; rfl
  have hP0 : P.det ≠ 0 := by
    rw [hdetP]
    exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hunit.ne_zero
  have hC0 : C.det ≠ 0 := fun h => hP0 (by rw [hdetP', h, zero_mul])
  have hM0 : iK M.det ≠ 0 := fun h => hP0 (by rw [hdetP', h, mul_zero])
  refine ⟨fun h => hM0 (by rw [h, map_zero]), hC0, ?_⟩
  rw [← vV_mul hC0 hM0, ← hdetP', hdetP]
  exact vV_algebraMap_unit T.V hunit

end GlobalTheory.TwoBasesDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertLagChar

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {κ : Type} [Fintype κ]

def diagW (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x) ∂μ

def lagInt (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) {N : ℕ} (ν : @Measure (Fin N → Fv F v) (borel _))
    (j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v)) (Φ : (κ ⊕ κ → Fv F v) → ℂ) : ℂ :=
  ∫ y, diagW ψ μ Φ (j y) ∂ν

open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct Matrix in
variable {F : Type} [Field F] [NumberField F] {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {κ : Type} [Fintype κ] in

theorem _root_.GlobalTheory.InertLagChar.diagW_zero (ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ℂ)
    (μ : @Measure (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (borel _)) (Φ : (κ ⊕ κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) :
    _root_.GlobalTheory.InertLagChar.diagW ψ μ Φ 0 = ∫ x, Φ (Sum.elim x x) ∂μ := by
  unfold _root_.GlobalTheory.InertLagChar.diagW _root_.GlobalTheory.WeilM.schr
  simp

end GlobalTheory.InertLagChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralEqNonzeroMulDiagonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalThetaIntegral_eq_nonzero_mul_diagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.DiagSiegelUnfold.diag_theta_integral | exact GlobalTheory.DiagSiegelUnfold.diag_theta_integral | (intros; apply GlobalTheory.DiagSiegelUnfold.diag_theta_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a : AF F),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a → a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
  first | exact @GlobalTheory.VacAny.eq_atPlace_of_at | exact GlobalTheory.VacAny.eq_atPlace_of_at | (intros; apply GlobalTheory.VacAny.eq_atPlace_of_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualSmallOfParts
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.Ind

theorem small_along : ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), AtAll PSeeEx 𝒜 σ → AtAll PPA 𝒜 σ → EvWC (fun _ => True) Small 𝒜 σ := by
  intro 𝒜 σ hS hP
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm CH hw _ _ => ⟨0, le_refl _, fun C _ => ?_⟩
  obtain ⟨x0, hx0⟩ := GlobalTheory.four_f_r_le_min_g_family _ Fm
  refine ⟨x0, fun x hx hx0' i => ?_⟩
  have hA := hx0 x hx0' hx i
  have hs := hS Fm (w3_a hw) x hx i
  have hp := hP Fm (w3_a hw) x hx i
  refine ⟨fun w hw1 => ((σ Fm (w3_a hw) x hx i).muDef C CH).2.2.2 w |>.2 hw1, ?_, ?_⟩
  · exact GlobalTheory.T.indefinite_scale_theta_limit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  · exact GlobalTheory.T.indefinite_scale_theta_degree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Fm.D x i).tcLL hA (σ Fm (w3_a hw) x hx i).ok1 hp.1 C CH
end GlobalTheory.Fc.Ind
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorAlongValuationPath
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem den_along_path : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) (Y : Scheme.{0}) (ζ : Sp (PowerSeries p.O) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U) (f : Γ(Y, U)), ∃ e ψ : PowerSeries p.O, PowerSeries.constantCoeff e ≠ 0 ∧ (⊤ ≤ ζ ⁻¹ᵁ U → e = 1) ∧ sc p u e * evAt (spMap (sc p u) ≫ ζ) h f = sc p u ψ := by
  intro k E _ _ _ p u Y ζ U h f
  obtain ⟨hcomp, -, hres, hloc, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  by_cases hU : ⊤ ≤ ζ ⁻¹ᵁ U
  · refine ⟨1, evAt ζ hU f, by simp, fun _ => rfl, ?_⟩
    rw [map_one, _root_.one_mul, hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U hU h f]
  · obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hy0, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (ζ (IsLocalRing.closedPoint (PowerSeries p.O)))) isOpen_univ
    have hζ0 : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (hloc _ _ _ _).2 hy0
    have hη0 : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := fun x _ => hζ0 (Set.mem_univ ((spMap (sc p u)) x))
    have hyU := (hloc _ _ _ _).1 h
    have hyU₀ := (hloc _ _ _ _).1 hη0
    obtain ⟨t, htU, hyt⟩ := hU₀.exists_basicOpen_le (V := U) ⟨_, hyU⟩ hyU₀
    have hηt : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ Y.basicOpen t := (hloc _ _ _ _).2 hyt
    haveI := hU₀.isLocalization_basicOpen t
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hmk⟩ := IsLocalization.mk'_surjective (Submonoid.powers t)
      (Y.presheaf.map (homOfLE htU).op f)
    have hspec := IsLocalization.mk'_spec Γ(Y, Y.basicOpen t) a (⟨t ^ n, n, rfl⟩ : Submonoid.powers t)
    simp only at hmk
    rw [hmk] at hspec
    have hle : Y.basicOpen t ≤ U₀ := Y.basicOpen_le t
    have key : evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE htU).op f) *
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op (t ^ n)) =
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op a) := by
      rw [← map_mul]; exact congrArg _ hspec
    have h1 := hres _ _ _ _ _ htU h hηt f
    have h2 := hres _ _ _ _ _ hle hη0 hηt (t ^ n)
    have h3 := hres _ _ _ _ _ hle hη0 hηt a
    have hu : IsUnit (evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op t)) :=
      (Y.toRingedSpace.isUnit_res_basicOpen t).map _
    refine ⟨evAt ζ hζ0 (t ^ n), evAt ζ hζ0 a, ?_, fun h' => absurd h' hU, ?_⟩
    · intro h0
      have hu' : IsUnit (sc p u (evAt ζ hζ0 (t ^ n))) := by
        rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h2, map_pow, map_pow]
        exact hu.pow n
      rw [PowerSeries.isUnit_iff_constantCoeff] at hu'
      apply hu'.ne_zero
      rw [sc, RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      simp
    · rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h1, ← h2, ← h3, ← key]
      exact mul_comm _ _

end GlobalTheory.Nef
end

