import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PeriodConstantPartEqZeroInjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem period_constantPart_eq_zero_injective {O : Type} [CommRing O] [StarRing O] (B : AnArc O) (la : B.La) (hy : la.y = 0)
    (h : B.P0 la = 0) : la = 0 := by
  have hl : la.l = 0 := by
    have := congrArg Prod.snd h
    rw [AnArc.degeneratingTori_basePeriodMap_snd, hy, map_zero, zero_add] at this
    exact Subtype.ext this
  refine AnArc.La.ext hy (AddMonoidHom.ext fun x => ?_) hl
  have : (B.P0 la).1 x = 0 := by rw [h]; rfl
  rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, hy, hl] at this
  simpa using this

theorem qkSt_of_ptSt : PtSt → QkSt := by
  intro hP O _ _ N B d k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP O N B d
  choose E hE hU using h1
  have hiff : ∀ v g, d.IsPt v g ↔ g = E v := fun v g => ⟨hU v g, fun h => h ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ la : B.La, E (B.P0 la) = N.io (d.eX la.y) := fun la => (hU _ _ (h5 la)).symm
  have hker : ∀ v v', E v = E v' → ∃ la : B.La, la.y = 0 ∧ v = v' + B.P0 la := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨la, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨la, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : B.V, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : B.V, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ (la : B.La) (p : N.QT k), d.Rep k la p ↔
      p.1.1.toAdd = d.eX la.y ∧ p.1.2 = E ((k : ℂ)⁻¹ • B.P0 la) := fun la p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun la => ?_, fun la la' p p' h h' => ?_, fun la la' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    have e : E (k • v) = E (B.P0 (AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0)) := by
      rw [hpow, hper, ← hv', AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      exact N.mem_QT.1 p.2
    obtain ⟨la, hy, hl⟩ := hker _ _ e
    refine ⟨AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0 + la, (hrep _ _).2 ⟨?_, ?_⟩⟩
    · rw [AnArc.La.add_y, hy, add_zero, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
    · rw [map_add, ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (d.eX la.y), E ((k : ℂ)⁻¹ • B.P0 la)), ?_⟩, (hrep _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    refine (hrep _ _).2 ⟨?_, ?_⟩
    · rw [AnArc.La.add_y, map_add, ← a, ← a']
      rfl
    · rw [map_add, smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      set z₀ : B.La := AnArc.La.mk (d.eX.symm z) 0 0 with hz₀
      have hz : d.eX z₀.y = z := by rw [hz₀, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      have e : E ((k : ℂ)⁻¹ • B.P0 la') = E ((k : ℂ)⁻¹ • B.P0 la + B.P0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨e₀, hy, hl⟩ := hker _ _ e
      refine ⟨z₀ + e₀, sub_eq_zero.1 (period_constantPart_eq_zero_injective B _ ?_ ?_)⟩
      · apply d.eX.injective
        rw [AnArc.La.sub_y, AnArc.La.add_y, AnArc.La.nsmul_y, AnArc.La.add_y, hy, add_zero, map_sub, map_add,
          map_nsmul, hz, ← a, ← a', c, sub_self, map_zero]
      · rw [map_sub, map_add, map_nsmul, map_add, ← hc2 (B.P0 la'), hl, add_assoc, smul_add, hc2, sub_self]
    · rintro ⟨e, rfl⟩
      refine ⟨d.eX e.y, ?_, ?_⟩
      · rw [a, a', AnArc.La.add_y, AnArc.La.nsmul_y, map_add, map_nsmul]
      · rw [b, b', map_add, map_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.Ex.Arch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisationGeneratingSectionPullbackLocalBase
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.GeneratorPull

theorem exists_down {X : Scheme.{0}} {L : LB X} (s : H0 L 1) : ∃ t : L.Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
    (J : (Z ⟶ X) → L.ι), Good L z J → sval s r z J = gs r z (L.U (J r)) (t.f (J r)) := by
  obtain ⟨b, hb⟩ := KeyBasis.exists_pw s
  exact ⟨KeyOnPol.ofPow b, fun Z r z J hJ =>
    (sval_of s r z J (fun _ => J r) fun _ => by rw [Category.comp_id]).trans (hb Z r z _ (hJ r))⟩

theorem exists_up {X : Scheme.{0}} {L : LB X} (t : L.Sec) : ∃ s : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
    (J : (Z ⟶ X) → L.ι), Good L z J → sval s r z J = gs r z (L.U (J r)) (t.f (J r)) := by
  obtain ⟨s, hs⟩ := KeyBasis.exists_powerSection_of_chartFunctions (KeyOnPol.toPow t)
  exact ⟨s, fun Z r z J hJ =>
    (sval_of s r z J (fun _ => J r) fun _ => by rw [Category.comp_id]).trans (hs Z r z _ (hJ r))⟩

theorem exists_generator_pull : Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (f : R →+* R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (Φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull Φ)), IsGrpPullback P'.A P.A (spMap f) Φ → w.IsGen → ∀ th : H0 P.L 1, (∀ s : H0 P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal P.A.hom r) * th.f j) → ∃ th' : H0 P'.L 1, (∀ s : H0 P'.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal P'.A.hom r) * th'.f j) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) (J' : (Z ⟶ P'.A.left) → P'.L.ι), Good P.L z J → Good P'.L z J' → sval th (r ≫ Φ) z J = (gw w r z (J (r ≫ Φ)) (J' r)).val * sval th' r z J' := by
  intro hL R R' _ _ _ _ f P P' Φ w hΦ hw th hth
  obtain ⟨b, hb, -⟩ := KeyOnPol.exists_generator hL.secBaseChange P
  obtain ⟨t, ht⟩ := exists_down th
  obtain ⟨β, hβ⟩ := exists_up b
  obtain ⟨a, ha⟩ := hth β
  have nz : ∀ y : Sp R, ∃ x : P.A.left, P.A.hom x = y ∧ x ∈ nonzeroLocus t := fun y => by
    obtain ⟨x, hx, hn⟩ := hb y
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hn
    obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB x (fun _ : PUnit => 𝟙 P.A.left) (fun _ => k) (fun _ _ _ => rfl)
      fun _ => hk
    obtain rfl : J (𝟙 _) = k := e PUnit.unit
    have h := IndivisibleSection.sval_of_secIsMul (p := P.A.hom) (a := a) (s := β) (t := th) ha (𝟙 _) x hJ
    rw [hβ _ _ x J hJ, ht _ _ x J hJ] at h
    exact ⟨x, hx, (mem_nonzeroLocus _ _).2 ⟨_, hk, isUnit_of_mul_isUnit_right (h ▸ u)⟩⟩
  obtain ⟨t', ht'⟩ := sec_pull_down ((isGen_iff w).1 hw) P.isLB P'.isLB t
  have nz' := SectionBaseChange.fibre_nonzero_of_pull P'.isLB ht' hΦ.1 nz
  obtain ⟨th', hth'⟩ := exists_up t'
  refine ⟨th', fun s => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_down s
    obtain ⟨c, hc, -⟩ := SectionBaseChange.generates hL.secBaseChange P hΦ.1 P'.isLB ⟨w, hw⟩ t' nz' σ
    refine ⟨c, IndivisibleSection.secIsMul_of_sval P'.isLB fun y J hJ => ?_⟩
    rw [hσ _ _ y J hJ, hth' _ _ y J hJ]
    exact (sec_eq_iff _ _ _ _).1 hc _ y (hJ (𝟙 _))
  · rw [ht _ _ z J hJ, hth' _ _ z J' hJ']
    exact ht' Z r z _ _ (hJ (r ≫ Φ)) (hJ' r)

end GlobalTheory.GeneratorPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianPullbackLineBundle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.Trait

theorem eq_of_comp_schemeDominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let f' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk f
  let g' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk g h.symm
  haveI : IsSeparated (Over.mk s).hom := ‹IsSeparated s›
  let d' : Over.mk (d ≫ f ≫ s) ⟶ Over.mk (f ≫ s) := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := Over.OverMorphism.ext hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  exact congrArg CommaMorphism.left ((cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g'))

theorem schemeDominant_spec_of_injective {A B : Type} [CommRing A] [CommRing B] [_root_.IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem act_comm_of_torsion : Laws → EndDeterminedOnTorsionSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Scheme.{0}) (s : Sp R ⟶ S) (B : PolAV (Sp R)) (B₀ : PolAV S) (ρ : letI := H.starRing; B.OAct (𝓞 E)) (ρ₀ : letI := H.starRing; B₀.OAct (𝓞 E)) (ψ : B.A.left ⟶ B₀.A.left), IsGrpPullback B.A B₀.A s ψ → LBIso B.L (B₀.L.pull ψ) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing R) C] (n : ℕ), 2 ≤ n → ∀ x : 𝓞 E, (letI := H.starRing; (∀ (j : ℕ) (y : TF (R := R) C ⟶ B.A), y ^ n ^ j = 1 → (y ≫ ρ.act x).left ≫ ψ = y.left ≫ ψ ≫ (ρ₀.act x).left) → (ρ.act x).left ≫ ψ = ψ ≫ (ρ₀.act x).left) := by
  intro hL h₂ E _ _ _ H R _ _ _ S s B B₀ ρ ρ₀ ψ hψ hw C _ _ _ _ n hn x h
  letI := H.starRing
  obtain ⟨ρ', hρ'⟩ := polOActPull _ _ s B₀ B ψ hψ hw.symm (𝓞 E) ρ₀
  obtain ⟨P, g, hg, -, hm, ht⟩ := hL.polBaseChange _ _ (TF (R := R) C).hom B
  have gp : IsGrpPullback P.A B.A (TF (R := R) C).hom g := ⟨hg, fun T a b a₀ b₀ ha hb => by
    have e₁ : a₀ = toBase hg.w a := Over.OverMorphism.ext ha
    have e₂ : b₀ = toBase hg.w b := Over.OverMorphism.ext hb
    rw [e₁, e₂, ← hm]; rfl⟩
  obtain ⟨σ, hσ⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ
  obtain ⟨σ', hσ'⟩ := polOActPull _ _ _ B P g gp ht (𝓞 E) ρ'
  obtain ⟨c, hc⟩ := exists_starNormLE_of_isCMField E (fun a => H.bar_eq a) x
  set j := 4 ^ P.g * P.g.factorial * (2 * c) with hj
  have hlt : j < (n ^ j) ^ 2 := (Nat.lt_pow_self hn).trans_le (Nat.le_self_pow two_ne_zero _)
  have key := h₂ P.g c (n ^ j) hlt C (Nat.cast_ne_zero.2 (by positivity)) P P rfl rfl (Iso.refl _)
    (ThetaPtDet.isPolIso_refl P) _ σ σ' x hc fun y hy => by
      let u : TF (R := R) C ⟶ Over.mk ((baseOver (Sp C)).hom ≫ (TF (R := R) C).hom) :=
        Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
      let z : TF (R := R) C ⟶ B.A := u ≫ pushHom gp _ y
      have hz : z.left = y.left ≫ g := Category.id_comp _
      have hz' : z ^ n ^ j = 1 := by
        rw [← MonObj.comp_pow, ← map_pow, hy, map_one, MonObj.comp_one]
      have e := h j z hz'
      rw [← hρ', ← Category.assoc, ← Over.comp_left] at e
      have e' : (z ≫ ρ.act x).left = (z ≫ ρ'.act x).left := hψ.1.hom_ext e (by rw [Over.w, Over.w])
      rw [Iso.refl_hom, Category.comp_id, Category.id_comp]
      refine Over.OverMorphism.ext (hg.hom_ext ?_ (by rw [Over.w, Over.w]))
      rw [Over.comp_left _ _ _ z, Over.comp_left _ _ _ z, hz] at e'
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hσ, hσ']
      simpa only [Category.assoc] using e'
  rw [Iso.refl_hom, Category.comp_id, Category.id_comp] at key
  haveI : IsSchemeTheoreticallyDominant (jK R) := schemeDominant_spec_of_injective _ (IsFractionRing.injective R _)
  haveI : IsSchemeTheoreticallyDominant (jFK (R := R) C) := schemeDominant_spec_of_injective _ (RingHom.injective _)
  haveI : IsSchemeTheoreticallyDominant (TF (R := R) C).hom := by
    show IsSchemeTheoreticallyDominant (_ ≫ _); infer_instance
  haveI := B.isAb.proper
  haveI := B.isAb.smooth
  haveI : QuasiCompact (TF (R := R) C).hom := by
    show QuasiCompact (spMap (algebraMap (FractionRing R) C) ≫ spMap (algebraMap R (FractionRing R))); infer_instance
  haveI : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isPullback hg.flip
  rw [← hρ', eq_of_comp_schemeDominant B.A.hom ((Over.w (ρ.act x)).trans (Over.w (ρ'.act x)).symm) g
    (by rw [← hσ, ← hσ', key])]

end GlobalTheory.Ex.Trait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Reframe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem reframe : ThetaUnifAV → ReframeSt := by
  intro hT Q L₀ g u₀ _ _ _
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, ht₁, ht₂, -, -, hEf, -⟩ := hT Q rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb L₀ Q.L g Q.g u₀ u ht₁ ht₂
    (𝟙 _) inferInstance
  have hF : ∀ z, u.ex (F z) = u₀.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ u₀.Λ := fun z => by rw [← u.ker, hF, u₀.ker]
  have cΛ : (u.Λ : Set (Fin Q.g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cΛ₀ : (u₀.Λ : Set (Fin g → ℂ)).Countable := by
    have := u₀.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u₀.Λ)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    FibreUnif.eq_zero_of_smul_mem_countable cΛ₀ fun t =>
      (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := FibreUnif.surjective_of_countable F cΛ fun v => by
    obtain ⟨z, hz⟩ := u₀.ex_onto (u.ex v)
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hz] at this
    exact right_eq_mul.1 this
  exact ⟨u, Hm, χ, Ef, LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩, hAH, hEf, hF⟩

end GlobalTheory.Ex.Arch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidifiedBundleTwoPullbacksCompare
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Compare

theorem eSec_comm_of_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem wVal_tri {X X' X'' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
    (T : Tri w w' w'') (y : Y) {J J' J''} (hJ : Good L y J) (hJ' : Good L' y J') (hJ'' : Good L'' y J'')
    (a : Y ⟶ X'') : GlobalTheory.ConstFam.wVal w'' y J J'' a =
      GlobalTheory.ConstFam.wVal w y J J' (a ≫ F') * GlobalTheory.ConstFam.wVal w' y J' J'' a := by
  have := T Y a y (J (a ≫ F' ≫ F)) (J' (a ≫ F')) (J'' a) (hJ (a ≫ F' ≫ F)) (hJ' (a ≫ F')) (hJ'' a)
  simpa only [GlobalTheory.ConstFam.wVal, Category.assoc] using this

theorem rigPull_compare : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (S S' : Scheme.{0}) (x : S ⟶ Z) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → ∀ (φ : G.left ⟶ G₀.left) (φ' : G'.left ⟶ G₀.left) (w : LB.Iso L (L₀.pull φ)) (w' : LB.Iso L' (L₀.pull φ')) ρ ρ', RigPull G G₀ x φ w ρ ρ₀ → RigPull G' G₀ (f ≫ x) φ' w' ρ' ρ₀ → ∃ (ψ : G'.left ⟶ G.left) (ω : LB.Iso L' (L.pull ψ)), RigPull G' G f ψ ω ρ' ρ ∧ ∀ (k : ℕ) (T₀ : Over Z) (T : Over S) (T' : Over S') (p : T.left ⟶ T₀.left) (q : T'.left ⟶ T.left), p ≫ T₀.hom = T.hom ≫ x → q ≫ T.hom = T'.hom ≫ f → ∀ s₀ s s', Thru w k (T' := T) (T := T₀) p s₀ s → Thru w' k (T' := T') (T := T₀) (q ≫ p) s₀ s' → Thru ω k (T' := T') (T := T) q s s' := by
  intro Z G₀ _ L₀ hL₀ ρ₀ S S' x f G _ G' _ L L' hL hL' φ φ' w w' ρ ρ' ⟨gp, hw, hρ, hm⟩ ⟨gp', hw', hρ', hm'⟩
  obtain ⟨ψ, e₁, e₂⟩ : ∃ ψ : G'.left ⟶ G.left, ψ ≫ φ = φ' ∧ ψ ≫ G.hom = G'.hom ≫ f :=
    ⟨gp.1.lift φ' (G'.hom ≫ f) (by rw [gp'.1.w, Category.assoc]), gp.1.lift_fst _ _ _, gp.1.lift_snd _ _ _⟩
  subst e₁
  have gψ : IsGrpPullback G' G f ψ := gp.cancel gp' e₂
  have pw := (isGen_iff w).1 hw
  have pw' := (isGen_iff w').1 hw'
  obtain ⟨ω, T⟩ := exists_cancel hL₀ w w' pw pw' hL hL'
  refine ⟨ψ, ω, ⟨gψ, (isGen_iff ω).2 (T.pgen_cancel hL₀ pw pw'), hρ',
    T.pmaps_cancel hL₀ (fun _ => eSec_comm_of_pullback gψ) hm hm'⟩, ?_⟩
  intro k T₀ T₁ T' p q hp hq s₀ s s' H H' Y r' r h₁ h₂ z J J' hJ hJ'
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.ConstFam.exists_good' hL₀ z
  have hw₀ : (r ≫ (fst T₁ G).left ≫ p) ≫ T₀.hom = (r ≫ (snd T₁ G).left ≫ φ) ≫ G₀.hom := by
    simp only [Category.assoc]
    rw [hp, gp.1.w, ← Category.assoc (fst T₁ G).left, ← Category.assoc (snd T₁ G).left, Over.w, Over.w]
  obtain ⟨r₀, a₁, a₂⟩ : ∃ r₀ : Y ⟶ (T₀ ⊗ G₀).left, r₀ ≫ (fst T₀ G₀).left = r ≫ (fst T₁ G).left ≫ p ∧
      r₀ ≫ (snd T₀ G₀).left = r ≫ (snd T₁ G).left ≫ φ :=
    ⟨pullback.lift _ _ hw₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have b₁ := H Y r r₀ a₁ a₂ z J₀ J hJ₀ hJ
  have b₂ := H' Y r' r₀ (by rw [a₁, ← Category.assoc, h₁]; simp only [Category.assoc])
    (by rw [a₂, ← Category.assoc, h₂]; simp only [Category.assoc]) z J₀ J' hJ₀ hJ'
  rw [wVal_tri T z hJ₀ hJ hJ', Category.assoc, ← h₂, b₁, Units.val_mul, mul_pow, _root_.mul_assoc,
    ← Units.val_pow_eq_pow_val] at b₂
  exact (Units.mul_right_inj _).1 b₂

end GlobalTheory.OneBasis.Compare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionNonzeroClosedFibreGeneratesExpansionZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.PrimitiveExpansion

theorem secLin_one {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    {R : Type} [CommRing R] (π : Y' ⟶ Spec (CommRingCat.of R))
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1) :
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ (fun _ : Fin 1 => s₂) h (fun _ => scal π (1 : R)) := by
  intro j₁ j₂ hc
  have e : scal π (1 : R) = 1 := by simp [scal]
  have := H j₁ j₂ hc
  rw [Fin.sum_univ_one, e, this]
  simp only [map_one, _root_.one_mul]

theorem main : LL → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : H0 U.LG.L 1, (∃ g, G.hom g = closedPoint V ∧ g ∈ nonzeroLocus σ) → (∀ s : H0 U.LG.L 1, ∃ b : V, SecIsMul G.hom b s σ) ∧ ∀ σ' : U.SecGF F 1, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) → ∃ ϑ, U.ExpandsG F 1 σ' ϑ ∧ Prim D Q v ϑ := by
  intro hL V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U σ ⟨x, hx, hn⟩
  obtain ⟨g, hE, hnd, H⟩ := GlobalTheory.NonzeroClosedFibre.main hL.1.globalFns V ϖ hϖ D Q hQ A G U σ
    (ThetaUnit.nonzeroOnSpecial_of_mem U σ x hx hn)
  have hgen := GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd hL.1.secBaseChange V ϖ hϖ D (g 0)
    (fun ⟨g', h'⟩ => hnd ⟨g', fun j => (h' j).trans rfl⟩)
  refine ⟨fun s => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨Φ, hΦ, -⟩ := H (FractionRing V) (GlobalTheory.FamInt.ordVal hϖ) (GlobalTheory.FamInt.valOver_ordVal hϖ)
    obtain ⟨b, hb⟩ := ThetaUnit.exists_eq_smul_group hL.1.globalFns le_rfl U hE
      (fun α => (ThetaUnit.secScal_one_iff D.toPre Φ α _).1 (hΦ α))
      (fun t => (hgen t).exists.imp fun b hb => (ThetaUnit.secIsMul_iff _ _ _ _).1 hb) s
    exact ⟨b, (ThetaUnit.secIsMul_iff _ _ _ _).2 hb⟩
  · obtain ⟨ϑ, hϑ, h₀, h₁⟩ := H F v hv
    refine ⟨ϑ, ⟨1, fun _ => 1, fun _ => σ, fun _ => g, fun _ => hE, secLin_one _
      (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_), fun α => secLin_one _ (hϑ α)⟩, h₀,
      fun r hr h => h₁ ⟨r, hr, h⟩⟩
    rw [Category.id_comp]
    exact (hσ' y J hJ).symm

end GlobalTheory.Ex.PrimitiveExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ShortestRepresentativesFormSumDependsOnLattice
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis.ShortSum

variable {X : Type} [AddCommGroup X]

abbrev mulSub (X : Type) [AddCommGroup X] (k : ℕ) : AddSubgroup X := (nsmulAddMonoidHom (α := X) k).range

theorem mk_eq_iff (k : ℕ) (a b : X) :
    (QuotientAddGroup.mk a : X ⧸ mulSub X k) = QuotientAddGroup.mk b ↔ ∃ z, b = a + k • z := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : k • z = -a + b := hz
    rw [this]; abel
  · rintro ⟨z, rfl⟩
    exact ⟨z, by simp⟩

theorem surj {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Function.Surjective (fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)) := by
  intro c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨i, z, hz⟩ := h.2.2.1 a
  exact ⟨i, (mk_eq_iff k _ _).2 ⟨z, hz⟩⟩

theorem sum_comp {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu)
    [Fintype (X ⧸ mulSub X k)] (g : X ⧸ mulSub X k → ℤ) :
    ∑ i, g (QuotientAddGroup.mk (cls i)) = mu * ∑ c, g c := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨i₀, rfl⟩ := surj h c
  rw [Finset.sum_congr rfl (g := fun _ => g (QuotientAddGroup.mk (cls i₀)))
    (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← h.2.2.2 i₀, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine Finset.filter_congr fun i _ => ⟨fun hi => ?_, fun hi => by simp only [hi]⟩
  exact h.2.1 i i₀ ((mk_eq_iff k _ _).1 hi.symm)

theorem val_eq {k r r' mu mu' : ℕ} {Q : X → ℤ} {cls : Fin r → X} {cls' : Fin r' → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') {i : Fin r} {i' : Fin r'}
    (e : (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k) = QuotientAddGroup.mk (cls' i')) :
    Q (cls i) = Q (cls' i') := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e
    rw [hz]; exact h.1 i z
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e.symm
    rw [hz]; exact h'.1 i' z

theorem sum_eq {k r mu mu' : ℕ} {Q : X → ℤ} {cls cls' : Fin r → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') : ∑ i, Q (cls i) = ∑ i, Q (cls' i) := by
  haveI : Finite (X ⧸ mulSub X k) := Finite.of_surjective _ (surj h)
  letI : Fintype (X ⧸ mulSub X k) := Fintype.ofFinite _
  have a := sum_comp h (fun _ => 1)
  have a' := sum_comp h' (fun _ => 1)
  have hm : (mu : ℤ) = mu' := by
    have hp : (∑ _c : X ⧸ mulSub X k, (1 : ℤ)) ≠ 0 := by simp
    exact mul_right_cancel₀ hp (a.symm.trans a')
  have b := sum_comp h (fun c => Q (cls (Function.surjInv (surj h) c)))
  have b' := sum_comp h' (fun c => Q (cls (Function.surjInv (surj h) c)))
  calc ∑ i, Q (cls i) = _ := Finset.sum_congr rfl fun i _ =>
        val_eq h h (Function.surjInv_eq (surj h) _).symm
    _ = _ := b
    _ = _ := by rw [hm]
    _ = _ := b'.symm
    _ = _ := Finset.sum_congr rfl fun i _ => val_eq h h' (Function.surjInv_eq (surj h) _)

theorem transport {X₀ : Type} [AddCommGroup X₀] {q₀ : X₀ → ℤ} {Q : X → ℤ} (e : X₀ ≃+ X) {w : ℕ} (hw : 0 < w)
    (hQ : ∀ y, Q (e y) = w * q₀ y) {k r mu : ℕ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Adapted k q₀ (fun i => e.symm (cls i)) mu := by
  refine ⟨fun i z => ?_, fun i i' ⟨z, hz⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩
  · have h1 := h.1 i (e z)
    have h2 := hQ (e.symm (cls i))
    have h3 := hQ (e.symm (cls i) + k • z)
    rw [map_add, map_nsmul] at h3
    rw [e.apply_symm_apply] at h2 h3
    rw [h2, h3] at h1
    exact le_of_mul_le_mul_left h1 (by exact_mod_cast hw)
  · have h1 := congrArg e hz
    simp only [map_add, map_nsmul, e.apply_symm_apply] at h1
    simp only [h.2.1 i i' ⟨_, h1⟩]
  · obtain ⟨i, z, hz⟩ := h.2.2.1 (e α)
    refine ⟨i, e.symm z, e.injective ?_⟩
    simp only [map_add, map_nsmul, e.apply_symm_apply]
    exact hz
  · rw [← h.2.2.2 i₀]
    simp only [e.symm.injective.eq_iff]

end GlobalTheory.OneBasis.ShortSum

namespace GlobalTheory.OneBasis

theorem sum_adapted_eq : ∀ (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (q₀ : X₀ → ℤ) (k r : ℕ), 1 ≤ k → (∀ y, 0 ≤ q₀ y) → ∃ d C : ℕ, 1 ≤ d ∧ ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (e : X₀ ≃+ X) (w : ℕ), 0 < w → (∀ y, Q (e y) = w * q₀ y) → ∀ (cls : Fin r → X) (mu : ℕ), Adapted k Q cls mu → (d : ℤ) * ∑ i, Q (cls i) = C * w * k := by
  intro X₀ _ _ _ q₀ k r hk hq
  by_cases hex : ∃ (c₀ : Fin r → X₀) (m₀ : ℕ), Adapted k q₀ c₀ m₀
  · obtain ⟨c₀, m₀, h₀⟩ := hex
    refine ⟨k, (∑ i, q₀ (c₀ i)).toNat, hk, fun X _ Q e w hw hQ cls mu h => ?_⟩
    rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hq _),
      ShortSum.sum_eq h₀ (ShortSum.transport e hw hQ h)]
    have : ∑ i, Q (cls i) = w * ∑ i, q₀ (e.symm (cls i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hQ, e.apply_symm_apply]
    rw [this]; ring
  · exact ⟨k, 0, hk, fun X _ Q e w hw hQ cls mu h => (hex ⟨_, _, ShortSum.transport e hw hQ h⟩).elim⟩

end GlobalTheory.OneBasis
end

