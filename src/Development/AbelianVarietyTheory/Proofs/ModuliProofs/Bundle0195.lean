import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelUp

theorem eq_constPt_of_formallyUnramified {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    (x : Sp (DualNumber k) ⟶ X) (h : x ≫ f = Geo.Tor.constPt (x ≫ f)) : x = Geo.Tor.constPt x := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  have := IsClosedImmersion.spec_of_surjective π hπ
  refine FormallyUnramified.hom_ext (Spec.map π) (isNilpotent_ker_specMap π hn) f ?_
    (h.trans (by simp only [Geo.Tor.constPt, Category.assoc]))
  have e : Spec.map π ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [Geo.Tor.constPt, ← Category.assoc, e, Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem formallyUnramified_spMap (j : KA l →+* KA l₂) : FormallyUnramified (spMap j) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := finiteDimensional_KA l₂
  have : Algebra.FormallyUnramified ℚ (KA l₂) := Algebra.FormallyUnramified.of_isSeparable ℚ (KA l₂)
  let _ : Algebra (KA l) (KA l₂) := j.toAlgebra
  exact Algebra.FormallyUnramified.of_restrictScalars ℚ (KA l) (KA l₂)

theorem exists_obj_of_eq {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s s' : S ⟶ Sp B} (e : s = s')
    (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o (𝟙 S)) := by
  subst e
  exact ⟨o, ⟨ObjComp.objMapId o⟩⟩

theorem nonempty_objMap_of_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f g : S' ⟶ S}
    (e : f = g) (m : ObjMap o' o f) : Nonempty (ObjMap o' o g) := by
  subst e
  exact ⟨m⟩

theorem exists_objMap_lower {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj D l b s} {o₂ : Obj D l₂ b₂ s₂} {o' : Obj D l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    ∃ n : ObjMap (ObjLower.lower o' h hρ hζ) o (g ≫ π), n.toSABMap.φ = u.toSABMap.φ ≫ m.φ := by
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩, hn⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₁ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.eta_add, ← ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₂ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.etaA_add, ← ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

end GlobalTheory.LevelUp

namespace GlobalTheory

open LevelUp

theorem nonempty_moduli_of_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  intro hL _ E _ _ _ H D l l₂ hpq hd ⟨Xo⟩
  have hA : l.A ∣ l₂.A := hd.2.2
  let j := levelFieldIncl hA
  let b := baseOfFinerLevel hA
  have hρ : b.ρ = (baseKA l₂).ρ := baseOfFinerLevel_rho hA
  have hζ : b.ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := baseOfFinerLevel_zeta hA
  have jρ : j (baseKA l).ρ = b.ρ := levelFieldIncl_rho hA
  have jζ : j (baseKA l).ζ = b.ζ := levelFieldIncl_zeta hA
  obtain ⟨o₁, ⟨m₀⟩⟩ := obj_pull E H D l _ _ (baseKA l) b j _ _ Xo.s (pullback.snd Xo.s (spMap j))
    (pullback.fst Xo.s (spMap j)) jρ jζ pullback.condition Xo.univ
  obtain ⟨S₂, π, o₂, m, hfin, het, -, ⟨h₁, h₂⟩, huniv⟩ :=
    GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ b (baseKA l₂) _ _ o₁ hpq hd hρ hζ
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  refine ⟨{ X := S₂, s := π ≫ pullback.snd Xo.s (spMap j), qproj := ?_, smooth := ?_, univ := o₂,
            rep := ?_, unram := ?_ }⟩
  · exact isQProjOver_comp_of_isFinite_noetherian _ _ _ _ _ hfin
      ((isQProjOver_baseChange_and_finite_restrict _ _ j _ Xo.s).1 Xo.qproj)
  · have : SmoothOfRelativeDimension (0 + D.dim) (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
    rwa [zero_add] at this
  · intro S t hS o
    obtain ⟨f₀, ⟨hf₀, ⟨n⟩⟩, hu₀⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo _ b j S t
      (ObjLower.lower o hd hρ hζ) hS jρ jζ
    obtain ⟨f, hf₁, hf₂⟩ : ∃ f : S ⟶ pullback Xo.s (spMap j), f ≫ pullback.fst _ _ = f₀ ∧ f ≫ pullback.snd _ _ = t :=
      ⟨pullback.lift f₀ t hf₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    subst hf₁ hf₂
    obtain ⟨m', -⟩ := ObjComp.objMap_cancel m₀ n
    obtain ⟨h, ⟨hh, u, -⟩, hu⟩ := huniv S f o m'.toSABMap ⟨m'.eta, m'.etaA⟩
    refine ⟨h, ⟨by rw [← Category.assoc, hh], ⟨u⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨v⟩⟩
    obtain ⟨w, hw⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ v
    obtain ⟨w', -⟩ := ObjComp.objMap_comp m₀ w
    have e : g ≫ π = f := by
      refine pullback.hom_ext (hu₀ _ ⟨?_, ⟨w'⟩⟩) (by rw [Category.assoc, hg])
      rw [Category.assoc, pullback.condition, ← hg]
      simp only [Category.assoc]
    subst e
    refine hu g ⟨rfl, v, hw.symm.trans ?_⟩
    exact obj_rigid_closed hL E H D l _ _ b b _ _ _ _ o₁ (ObjLower.lower o hd hρ hζ) (g ≫ π) (Or.inl hS)
      w.toSABMap m'.toSABMap fun a => ⟨_, w.eta a, m'.eta a⟩
  · rintro k _ x o ⟨u⟩ ⟨u'⟩
    have hj := formallyUnramified_spMap j
    have hp : FormallyUnramified (pullback.fst Xo.s (spMap j)) :=
      (HasRingHomProperty.isStableUnderBaseChange (P := @FormallyUnramified.{0})
        RingHom.FormallyUnramified.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip hj
    have hr : FormallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hp
    refine eq_constPt_of_formallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) x ?_
    obtain ⟨w, -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u
    obtain ⟨w', -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u'
    have e : (x ≫ π ≫ pullback.snd Xo.s (spMap j)) ≫ spMap j = (x ≫ π ≫ pullback.fst Xo.s (spMap j)) ≫ Xo.s := by
      simp only [Category.assoc, pullback.condition]
    obtain ⟨o', ⟨i⟩⟩ := exists_obj_of_eq e (objRestrictBase j (ObjLower.lower o hd hρ hζ) jρ jζ)
    let i' : ObjMap o' (ObjLower.lower o hd hρ hζ) (𝟙 _) := ⟨i.toSABMap, i.eta, i.etaA⟩
    obtain ⟨n, -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w).choose i'
    obtain ⟨n', -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w').choose i'
    exact Xo.unram k _ o' (nonempty_objMap_of_eq (by simp only [Category.assoc, Category.id_comp]) n)
      (nonempty_objMap_of_eq (by simp only [Geo.Tor.constPt, Category.assoc, Category.id_comp]) n')

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamRep

theorem spMap_surj {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ β : R →+* R', spMap β = x :=
  ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

open MvPolynomial in

theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => c * x j) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o}

theorem isTM_unique (hL : Out.Laws) (hL2 : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] [IsReduced R] (z : Sp R ⟶ S) (sw : Sp R ⟶ Sp o)
    (e : z ≫ s = sw) (w : TObj g (N' ^ 2) J b sw) (φ φ' : w.A.left ⟶ t.A.left) (h : IsTM w t z φ)
    (h' : IsTM w t z φ') : φ = φ' := by
  obtain ⟨β, rfl⟩ := spMap_surj sw
  obtain ⟨w', hw'⟩ := tObj_pull o g _ J b _ _ s _ z t e
  obtain ⟨ψ, hψ⟩ := tMap_iff.1 hw'
  obtain ⟨χ, rfl, hχ⟩ := hψ.cancel (h.congr (Category.id_comp z).symm rfl)
  obtain ⟨χ', rfl, hχ'⟩ := hψ.cancel (h'.congr (Category.id_comp z).symm rfl)
  rw [(GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β w w' hm hd ho ?_).2 χ χ' hχ.1 hχ'.1 hχ.2.1 hχ'.2.1
    fun i => (hχ.2.2.1 i).trans (hχ'.2.2.1 i).symm]
  refine Dense.mono (fun p _ => ?_) dense_univ
  obtain ⟨u, hu⟩ := tObj_pull o g _ J b _ _ _ _ ((Sp R).fromSpecResidueField p) w rfl
  refine ⟨(Sp R).residueField p, inferInstance, (Sp R).fromSpecResidueField p, u, ?_, hu, ?_⟩
  · exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply _ _⟩
  · have := tMap_comp hu (tMap_iff.2 ⟨_, hχ⟩)
    rwa [Category.comp_id] at this

theorem exists_hasTh_field (hL : Out.Laws) (hL2 : Out.Laws2) (ho : Odd N') (t : TObj g (N' ^ 2) J b s)
    (K : Type) [Field K] (y : Sp K ⟶ S) : ∃ v, t.HasTh y v := by
  obtain ⟨R, _, x, v, hx, hp, hv⟩ := ThetaLocal.exists_hasTh hL hL2 o g N' J b S s t ho (y (IsLocalRing.closedPoint K))
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) q (IsLocalRing.closedPoint K)]
  obtain ⟨ρ, hρ⟩ := spMap_surj (IsOpenImmersion.lift x y hr)
  have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ρ x v hv
  rw [hρ, IsOpenImmersion.lift_fac] at this
  exact ⟨_, this⟩

theorem eval_eq_zero_of_fromC (hL : Out.Laws) (hL2 : Out.Laws2) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N')
    {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    (t : TObj g (N' ^ 2) J b s) {K : Type} [Field K] (y : Sp K ⟶ S) (hy : FromC em C t y) (β : o →+* K)
    (hβ : y ≫ s = spMap β) (v : Ix g (N' ^ 2) → K) (hv : t.HasTh y v) :
    ∀ F ∈ thIdeal em C, MvPolynomial.eval₂ β v F = 0 := by
  obtain ⟨K₀, _, β₀, i, j, t₀, tx, tc, hj, hi, h1, h2, h3, hC⟩ := hy
  obtain ⟨v₀, hv₀⟩ := exists_hasTh_field hL hL2 ho t₀ K₀ (𝟙 _)
  have a1 : tx.HasTh (𝟙 _) v := (hasTh_iff_of_tmap o g N' J b _ _ t _ _ tx y K _ v h1).2 (by rwa [Category.id_comp])
  have a2 : tx.HasTh (𝟙 _) (fun a => i (v₀ a)) := (hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tx _ K _ _ h2).2 (by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ K i _ v₀ hv₀
    rwa [Category.comp_id, ← Category.id_comp (spMap i)] at this)
  have a3 : tc.HasTh (𝟙 _) (fun a => j (v₀ a)) := (hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tc _ ℂ _ _ h3).2 (by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ ℂ j _ v₀ hv₀
    rwa [Category.comp_id, ← Category.id_comp (spMap j)] at this)
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ tx n K _ _ ⊥ hn hd a2 Ideal.isPrime_bot 0
  obtain ⟨u, hu⟩ := hasTh_unique_unit hL hL2 o g N' J b _ _ tx K _ _ _ a2 a1
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit (by simpa using hc)))
  obtain rfl : β = i.comp β₀ := spMap_inj (hβ.symm.trans (hi.trans (spMap_comp_eq _ _)))
  obtain rfl : v = fun a => (u : K) * i (v₀ a) := funext hu
  intro F hF
  rw [← F.sum_homogeneousComponent, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hG := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF e
  have h0 : MvPolynomial.eval₂ em (fun a => j (v₀ a)) (MvPolynomial.homogeneousComponent e F) = 0 := by
    simp only [thIdeal, Ideal.mem_iInf] at hG
    exact hG tc _ ⟨hC, a3⟩
  have h4 : MvPolynomial.eval₂ β₀ v₀ (MvPolynomial.homogeneousComponent e F) = 0 := by
    apply j.injective
    rw [MvPolynomial.eval₂_comp_left, hj, map_zero]
    exact h0
  rw [eval₂_scale _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous e F)]
  have h5 := congrArg i h4
  rw [MvPolynomial.eval₂_comp_left, map_zero] at h5
  exact mul_eq_zero_of_right _ h5

theorem dense_affine {k : ℕ} {b : TBase o k} {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {t : TObj g k J b s}
    (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] (x : Sp R ⟶ S) [IsOpenImmersion x] :
    Dense {p : Sp R | ∃ (K : Type) (_ : Field K) (ψ : R →+* K), p ∈ Set.range (spMap ψ) ∧ FromC em C t (spMap ψ ≫ x)} := by
  refine Dense.mono (fun p hp => ?_) (hD.preimage x.isOpenEmbedding.isOpenMap)
  obtain ⟨K, _, y, ⟨q, hq⟩, hy⟩ := hp
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨q', rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) q' q, hq]
    exact ⟨p, rfl⟩
  obtain ⟨ρ, hρ⟩ := spMap_surj (IsOpenImmersion.lift x y hr)
  have e : spMap ρ ≫ x = y := by rw [hρ, IsOpenImmersion.lift_fac]
  refine ⟨K, inferInstance, ρ, ⟨q, x.isOpenEmbedding.injective ?_⟩, by rwa [e]⟩
  rw [← Scheme.Hom.comp_apply, e, hq]

theorem inMM_of_dense (hL : Out.Laws) (hL2 : Out.Laws2) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N')
    {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    {t : TObj g (N' ^ 2) J b s} (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] [IsReduced R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] (β : o →+* R) (hβ : x ≫ s = spMap β) (v : Ix g (N' ^ 2) → R) (hv : t.HasTh x v) :
    InMM n N' (thIdeal em C) β v := by
  refine ⟨fun F hF => ?_, fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n R x v q hn hd hv hq⟩
  by_contra hne
  have hb : PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F) ≠ ⊥ := fun h =>
    hne ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 h).eq_zero
  obtain ⟨p, ⟨K, _, ψ, ⟨q, rfl⟩, hy⟩, hp⟩ := (dense_affine hD x).exists_mem_open
    (PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F)).isOpen
    ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb)
  have h0 := eval_eq_zero_of_fromC hL hL2 hn hd ho hem t _ hy (ψ.comp β)
    (by rw [Category.assoc, hβ, spMap_comp_eq]) _ (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ψ x v hv) F hF
  refine hp (show ψ (MvPolynomial.eval₂ β v F) ∈ (show PrimeSpectrum K from q).asIdeal from ?_)
  rw [MvPolynomial.eval₂_comp_left]
  exact (show MvPolynomial.eval₂ (ψ.comp β) (ψ ∘ v) F = 0 from h0) ▸ Ideal.zero_mem _

theorem tMap_affine (hL : Out.Laws) (hL2 : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (w₀ : J) (hC : ∀ t, C t → t.Shape Mat κ) {M : Scheme.{0}} {sM : M ⟶ Sp o} (u : TObj g (N' ^ 2) J b sM)
    (hu : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M) (t' : TObj g (N' ^ 2) J b (x ≫ sM)) v,
      t'.Shape Mat κ → t'.HasTh (𝟙 _) v → u.HasTh x v → TMap t' u x)
    {t : TObj g (N' ^ 2) J b s} (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] [IsReduced R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] (y : Sp R ⟶ M) (hxy : y ≫ sM = x ≫ s) (v : Ix g (N' ^ 2) → R) (hv : t.HasTh x v)
    (hv' : u.HasTh y v) (w : TObj g (N' ^ 2) J b (x ≫ s)) (hw : TMap w t x) : TMap w u y := by
  obtain ⟨β, hβ⟩ := spMap_surj (x ≫ s)
  obtain ⟨tx, htx⟩ := tObj_pull o g _ J b _ _ s _ x t hβ.symm
  obtain ⟨ux, hux⟩ := tObj_pull o g _ J b _ _ sM _ y u (hxy.trans hβ.symm)
  have key : TMap tx ux (𝟙 _) := by
    refine (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β tx ux hm hd ho (Dense.mono (fun p hp => ?_) (dense_affine hD x))).1
    obtain ⟨K, _, ψ, ⟨q, rfl⟩, K₀, _, β₀, i, j, t₀, tK, tc, -, -, h1, h2, h3, hc⟩ := hp
    let a := algebraMap K (AlgebraicClosure K)
    have ez : spMap a ≫ spMap ψ = spMap (a.comp ψ) := spMap_comp_eq _ _
    obtain ⟨t', ht'⟩ := tObj_pull o g _ J b _ _ _ ((spMap (a.comp ψ) ≫ y) ≫ sM) (spMap (a.comp ψ)) tx
      (by rw [Category.assoc, hxy, hβ])
    obtain ⟨u', hu'⟩ := tObj_pull o g _ J b _ _ _ _ (spMap (a.comp ψ)) tx rfl
    have s0 : t₀.Shape Mat κ := ((GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tc h3).2.2 K₀ rfl
      inferInstance inferInstance).1 (hC tc hc)
    have s1 : tK.Shape Mat κ := (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tK h2).1 s0
    have m1 : TMap t' t (spMap (a.comp ψ) ≫ x) := tMap_comp ht' htx
    have m2 : TMap t' tK (spMap a) := tMap_cancel h1 (by rwa [← Category.assoc, ez])
    have s2 : t'.Shape Mat κ := (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ tK t' m2).1 s1
    have m3 : TMap t' u (spMap (a.comp ψ) ≫ y) := hu _ _ t' _ s2
      ((hasTh_iff_of_tmap o g N' J b _ _ t _ _ t' _ _ _ _ m1).2 (by
        rw [Category.id_comp]; exact GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R _ (a.comp ψ) x v hv))
      (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b M sM u R _ (a.comp ψ) y v hv')
    have m4 : TMap u' t' (𝟙 _) := tMap_cancel ht' (by rwa [Category.id_comp])
    have m5 := tMap_comp m4 m3
    rw [Category.id_comp] at m5
    refine ⟨AlgebraicClosure K, inferInstance, spMap (a.comp ψ), u', ⟨IsLocalRing.closedPoint _, ?_⟩, hu',
      tMap_cancel hux m5⟩
    rw [← ez]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum K) _ _))
  have m : TMap w tx (𝟙 _) := tMap_cancel htx (by rwa [Category.id_comp])
  have := tMap_comp (tMap_comp m key) hux
  rwa [Category.id_comp, Category.id_comp] at this

theorem family_universal : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  refine ⟨2, fun j hj o _ b em C d hem hC Y u hu hq S s' t hS hD => ?_⟩
  have ho : Odd (n ^ j) := hodd.pow
  have hd : n ^ 2 ∣ n ^ j := pow_dvd_pow n hj
  have hd1 : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hred : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ S), IsOpenImmersion x → _root_.IsReduced R := fun R _ x _ =>
    (affine_isReduced_iff (CommRingCat.of R)).1 (isReduced_of_isOpenImmersion x)
  have uniq : ∀ (R : Type) [CommRing R] (y y' : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), y ≫ Y.s = y' ≫ Y.s →
      u.HasTh y v → u.HasTh y' v → y = y' := by
    intro R _ y y' v e h h'
    obtain ⟨β, hβ⟩ := spMap_surj (y ≫ Y.s)
    exact (Y.pts R β v (Y.loc R β y v hβ.symm ((hu R y v).1 h))).unique ⟨hβ.symm, (hu R y v).1 h⟩
      ⟨e.symm.trans hβ.symm, (hu R y' v).1 h'⟩
  choose R cR x v hx hp hv using ThetaLocal.exists_hasTh hL hL2 o g _ J b S s' t ho
  have loc : ∀ p, ∃ y : Sp (R p) ⟶ Y.MM, y ≫ Y.s = x p ≫ s' ∧ u.HasTh y (v p) := fun p => by
    have := hx p
    have := hred _ _ (hx p)
    obtain ⟨β, hβ⟩ := spMap_surj (x p ≫ s')
    obtain ⟨y, ⟨h1, h2⟩, -⟩ := Y.pts _ β _ (inMM_of_dense hL hL2 hn.two_le hd1 ho hem.2.2 hD (x p) β hβ.symm _ (hv p))
    exact ⟨y, h1.trans hβ, (hu _ _ _).2 h2⟩
  choose y hy hy' using loc
  choose tx htx using fun p => tObj_pull o g _ J b _ _ s' _ (x p) t rfl
  have hty : ∀ p, TMap (tx p) u (y p) := fun p =>
    haveI := hx p
    haveI := hred _ _ (hx p)
    tMap_affine hL hL2 hn.two_le hd ho w (fun t ht => (hC.shape t ht).1) u
      (fun K _ _ x t' v h1 h2 h3 => hq K x t' v h1 h2 ((hu _ _ _).1 h3)) hD (x p) (y p) (hy p) (v p) (hv p) (hy' p)
      (tx p) (htx p)
  have tr : ∀ p (T : Type) [CommRing T] (a : Sp T ⟶ Sp (R p)) (c : Ix g ((n ^ j) ^ 2) → T),
      t.HasTh (a ≫ x p) c → u.HasTh (a ≫ y p) c := fun p T _ a c h =>
    (hasTh_iff_of_tmap o g _ J b _ _ u _ _ (tx p) _ T a c (hty p)).1
      ((hasTh_iff_of_tmap o g _ J b _ _ t _ _ (tx p) _ T a c (htx p)).2 h)
  obtain ⟨f, hf⟩ := exists_glue _ x y hx (fun p => ⟨p, hp p⟩) fun i i' q hq => by
    have := hx i
    have := hx i'
    obtain ⟨T, z, hz, ⟨r, hr⟩, hs⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (U := (x i).opensRange ⊓ (x i').opensRange) (x := x i q) ⟨⟨q, rfl⟩, hq⟩
    obtain ⟨a, e1⟩ : ∃ a : Sp T ⟶ Sp (R i), a ≫ x i = z :=
      ⟨_, IsOpenImmersion.lift_fac (x i) z (fun p hp => (hs hp).1)⟩
    obtain ⟨a', e2⟩ : ∃ a' : Sp T ⟶ Sp (R i'), a' ≫ x i' = z :=
      ⟨_, IsOpenImmersion.lift_fac (x i') z (fun p hp => (hs hp).2)⟩
    have : IsOpenImmersion (a ≫ x i) := by rw [e1]; exact hz
    refine ⟨_, a, a', IsOpenImmersion.of_comp a (x i), ⟨r, (x i).isOpenEmbedding.injective ?_⟩, e1.trans e2.symm, ?_⟩
    · rw [← Scheme.Hom.comp_apply, e1, hr]
    · obtain ⟨ρ, hρ⟩ := spMap_surj (R' := T) a
      have h := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g _ J b S s' t _ T ρ (x i) (v i) (hv i)
      rw [hρ] at h
      refine uniq T _ _ _ ?_ (tr i T a _ h) (tr i' T a' _ (by rw [e2, ← e1]; exact h))
      rw [Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ s') (e1.trans e2.symm)
  have hfs : f ≫ Y.s = s' := hom_ext_loc fun p => ⟨_, x p, hx p, hp p, by rw [← Category.assoc, hf, hy]⟩
  refine ⟨f, ⟨hfs, ?_⟩, fun f' hf' => hom_ext_loc fun p => ⟨_, x p, hx p, hp p, ?_⟩⟩
  · obtain ⟨u', hu'⟩ := tObj_pull o g _ J b _ _ Y.s s' f u hfs
    have := tMap_comp (tMap_of_loc hL.globalFns t u'
      (fun p => ⟨_, x p, tx p, hx p, hp p, htx p, tMap_cancel hu' (by rw [hf]; exact hty p)⟩)
      (fun t T _ z => tObj_pull o g _ J b _ _ s' _ z t rfl)
      (fun t T _ z w φ φ' hz h h' => haveI := hred T z hz
        isTM_unique hL hL2 hn.two_le hd ho t T z _ rfl w φ φ' h h')) hu'
    rwa [Category.id_comp] at this
  · rw [hf]
    exact uniq _ _ _ (v p) (by rw [Category.assoc, hf'.1, hy])
      ((hasTh_iff_of_tmap o g _ J b _ _ u _ _ t f' _ (x p) (v p) hf'.2).1 (hv p)) (hy' p)

end GlobalTheory.FamRep
end
end

