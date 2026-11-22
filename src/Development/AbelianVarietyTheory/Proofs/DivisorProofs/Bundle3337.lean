import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3327
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3328
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowerGaloisExtSymplecticLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.LevelPrimePower

theorem iterate_fixes {A : Type} [CommGroup A] (f : A →* A) (ℓ : ℕ) (hf : ∀ x, x ^ ℓ = 1 → f x = x) (e : ℕ) :
    ∀ x : A, x ^ ℓ ^ (e + 1) = 1 → f^[ℓ ^ e] x = x := by
  induction e with
  | zero => intro x hx; simpa using hf x (by simpa using hx)
  | succ e ih =>
    intro x hx
    let h : A →* A := ((show Monoid.End A from f) ^ ℓ ^ e : Monoid.End A)
    have hh : ∀ a, h a = f^[ℓ ^ e] a := fun a => congrFun (Monoid.End.coe_pow A f _) a
    have h1 : h x ^ ℓ = x ^ ℓ := by
      rw [← map_pow, hh]
      exact ih _ (by rw [← pow_mul, ← pow_succ', hx])
    have hy : (h x / x) ^ ℓ = 1 := by rw [div_pow, h1, div_self']
    have h2 : h (h x / x) = h x / x := by
      rw [hh]
      exact ih _ (by rw [pow_succ', pow_mul, hy, one_pow])
    have h3 : ∀ n : ℕ, h^[n] x = x * (h x / x) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        rw [Function.iterate_succ_apply', ihn, map_mul, map_pow, h2, pow_succ', ← _root_.mul_assoc,
          mul_div_cancel]
    have h4 : (h : A → A) = f^[ℓ ^ e] := funext hh
    rw [pow_succ, Function.iterate_mul, ← h4, h3, hy, _root_.mul_one]

theorem exists_normal {G A : Type} [Group G] [CommGroup A] (ρ : G → A →* A) (h1 : ∀ x, ρ 1 x = x)
    (hm : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x)) (ℓ e : ℕ) (hf : ∀ σ x, x ^ ℓ = 1 → ρ σ x = x) :
    ∃ H : Subgroup G, H.Normal ∧ (∀ σ, σ ^ ℓ ^ e ∈ H) ∧ ∀ σ ∈ H, ∀ x, x ^ ℓ ^ e = 1 → ρ σ x = x := by
  let H : Subgroup G :=
    { carrier := {σ | ∀ x, x ^ ℓ ^ e = 1 → ρ σ x = x}
      one_mem' := fun x _ => h1 x
      mul_mem' := fun {a b} ha hb x hx => by rw [hm, hb x hx, ha x hx]
      inv_mem' := fun {a} ha x hx => by
        conv_lhs => rw [← ha x hx, ← hm, inv_mul_cancel, h1] }
  refine ⟨H, ⟨fun a ha g x hx => ?_⟩, fun σ x hx => ?_, fun σ hσ => hσ⟩
  · rw [hm, hm, ha _ (by rw [← map_pow, hx, map_one]), ← hm, mul_inv_cancel, h1]
  · have hp : ∀ (n : ℕ) x, ρ (σ ^ n) x = (ρ σ)^[n] x := by
      intro n
      induction n with
      | zero => intro x; simpa using h1 x
      | succ n ih => intro x; rw [pow_succ, hm, ih, Function.iterate_succ_apply]
    rw [hp]
    exact iterate_fixes _ ℓ (hf σ) e x (by rw [pow_succ, pow_mul, hx, one_pow])

theorem exists_factor_fixedField {F L : Type} [Field F] [Field L] [Algebra F L] (H : Subgroup (L ≃ₐ[F] L))
    {Y : Scheme.{0}} (y : Sp L ⟶ Y) (h : ∀ σ ∈ H, spMap σ.toAlgHom.toRingHom ≫ y = y) :
    ∃ z : Sp (IntermediateField.fixedField H) ⟶ Y, spMap (algebraMap (IntermediateField.fixedField H) L) ≫ z = y := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L Y).symm.surjective y
  have hy : (Scheme.SpecToEquivOfField L Y).symm ⟨p, φ⟩ = Spec.map φ ≫ Y.fromSpecResidueField p := rfl
  rw [hy] at h ⊢
  have hmem : ∀ b, φ.hom b ∈ IntermediateField.fixedField H := by
    intro b
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 := h σ hσ
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp, Spec.map_inj] at h1
    exact congrArg (fun ψ => ψ.hom b) h1
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict (IntermediateField.fixedField H) hmem)) ≫
    Y.fromSpecResidueField p, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_intermediate {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {S : Scheme.{0}} (X : Over S) [GrpObj X] [IsCommMonObj X] (s₀ : Sp F ⟶ S) (s : Sp L ⟶ S)
    (hs : s = spMap (algebraMap F L) ≫ s₀) (ℓ e : ℕ) (hℓ : ℓ.Prime) (ζ₀ : F) (hζ : IsPrimitiveRoot ζ₀ ℓ)
    (hfix : ∀ z : Over.mk s ⟶ X, z ^ ℓ = 1 → ∃ w : Sp F ⟶ X.left, spMap (algebraMap F L) ≫ w = z.left) :
    ∃ M : IntermediateField F L, IsGalois F M ∧ (∃ d, Module.finrank F M = ℓ ^ d) ∧
      (∀ u : Lˣ, u ^ ℓ ^ e = 1 → (u : L) ∈ M) ∧
      ∀ z : Over.mk s ⟶ X, z ^ ℓ ^ e = 1 → ∃ w : Sp M ⟶ X.left, spMap (algebraMap M L) ≫ w = z.left := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hσ : ∀ σ : L ≃ₐ[F] L, spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap F L) = spMap (algebraMap F L) := by
    intro σ
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact σ.commutes a
  let t : (L ≃ₐ[F] L) → (Over.mk s ⟶ Over.mk s) := fun σ => Over.homMk (spMap σ.toAlgHom.toRingHom) (by
    show spMap σ.toAlgHom.toRingHom ≫ s = s
    rw [hs, ← Category.assoc, hσ])
  let ρ : (L ≃ₐ[F] L) → (Over.mk s ⟶ X) →* (Over.mk s ⟶ X) := fun σ =>
    { toFun := fun x => t σ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  have hρ : ∀ σ x, (ρ σ x).left = spMap σ.toAlgHom.toRingHom ≫ x.left := fun _ _ => rfl
  obtain ⟨H₁, n₁, p₁, f₁⟩ := exists_normal ρ
    (fun x => Over.OverMorphism.ext (by
      rw [hρ]
      exact (congrArg (· ≫ x.left) (Spec.map_id (CommRingCat.of L))).trans (Category.id_comp _)))
    (fun σ τ x => Over.OverMorphism.ext (by
      rw [hρ, hρ, hρ]
      erw [← Category.assoc, ← Spec.map_comp]
      rfl)) ℓ e
    (fun σ x hx => Over.OverMorphism.ext (by
      obtain ⟨w, hw⟩ := hfix x hx
      rw [hρ, ← hw]
      erw [← Category.assoc, hσ]))
  obtain ⟨H₂, n₂, p₂, f₂⟩ := exists_normal (fun σ : L ≃ₐ[F] L => Units.map σ.toAlgHom.toRingHom.toMonoidHom)
    (fun x => rfl) (fun σ τ x => rfl) ℓ e
    (fun σ x hx => Units.ext (by
      have hx' : (x : L) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
      obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap F L).injective).eq_pow_of_pow_eq_one hx'
      show σ (x : L) = x
      rw [← hi, ← map_pow, σ.commutes]))
  let H := H₁ ⊓ H₂
  haveI : H.Normal := inferInstanceAs (H₁ ⊓ H₂).Normal
  have hP : IsPGroup ℓ ((L ≃ₐ[F] L) ⧸ H) := by
    intro g
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨p₁ σ, p₂ σ⟩
  refine ⟨IntermediateField.fixedField H, inferInstance, ?_, fun u hu => ?_, fun z hz => ?_⟩
  · obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hP
    refine ⟨d, ?_⟩
    rw [← hd, ← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv).symm
  · rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => congrArg Units.val (f₂ σ hσ.2 u hu)
  · exact exists_factor_fixedField H _ fun σ hσ => congrArg CommaMorphism.left (f₁ σ hσ.1 z hz)

theorem exists_level_primePower : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (emb : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (ℓ M K : ℕ), ℓ.Prime → 0 < M → ℓ ∣ M → (∃ e, K = ℓ ^ e) → (∃ ζ₀ : Ω₁, IsPrimitiveRoot ζ₀ M) → (∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp R₁) (z : Over.mk x ⟶ P₁.A), z ^ M = 1 → ∃ y : baseOver (Sp R₁) ⟶ P₁.A, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₁)) ≫ y = z) → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ (∃ e, Module.finrank Ω₁ Ω₂ = ℓ ^ e) ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp emb)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  intro F _ _ R₁ _ emb P₁ ℓ N K hℓ hN hℓN ⟨e, hK⟩ ⟨ζ₀, hζ₀⟩ hsec
  have hK0 : 0 < K := hK ▸ pow_pos hℓ.pos e
  have := P₁.isAb.comm
  obtain ⟨L, _, _, Q₃, φ₃, ζ₃, hfd, hgal, hζ₃, -, h₃, -, ⟨lev⟩⟩ := LevelGalois.exists_level_galois emb P₁ K hK0
  obtain ⟨c, rfl⟩ := hℓN
  have hζ₁ : IsPrimitiveRoot (ζ₀ ^ c) ℓ := hζ₀.pow hN (Nat.mul_comm _ _)
  have hs : spMap ((algebraMap F L).comp emb) = spMap (algebraMap F L) ≫ spMap emb := (GlobalTheory.spMap_comp_spMap _ _).symm
  obtain ⟨M, hMgal, hdeg, hroot, hpts⟩ := exists_intermediate P₁.A (spMap emb) (spMap ((algebraMap F L).comp emb)) hs
    ℓ e hℓ _ hζ₁ (fun z hz => by
      let τ := algebraMap L (AlgebraicClosure L)
      let k : Over.mk (spMap τ ≫ spMap ((algebraMap F L).comp emb)) ⟶ Over.mk (spMap ((algebraMap F L).comp emb)) :=
        Over.homMk (spMap τ) rfl
      obtain ⟨y, hy⟩ := hsec _ _ (k ≫ z) (by rw [← MonObj.comp_pow, pow_mul, hz, one_pow, MonObj.comp_one])
      refine ⟨spMap emb ≫ y.left, spec_map_field_cancel τ _ _ ?_⟩
      have hy' : (spMap τ ≫ spMap ((algebraMap F L).comp emb)) ≫ y.left = spMap τ ≫ z.left :=
        congrArg CommaMorphism.left hy
      rw [← hy', hs]
      simp only [Category.assoc])
  rw [← hK] at hroot hpts
  haveI : CharZero M := (algebraMap F M).charZero_iff (algebraMap F M).injective |>.1 inferInstance
  have hB := GlobalTheory.laws_without_cohomology.2.2.1
  let ζ' : M := ⟨ζ₃, hroot ζ₃ hζ₃.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' K :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap M L) (IsPrimitiveRoot.coe_units_iff.2 hζ₃)
      (algebraMap M L).injective
  obtain ⟨ζ, hζe⟩ := hζ'.isUnit hK0.ne'
  have hζ : IsPrimitiveRoot ζ K := IsPrimitiveRoot.coe_units_iff.1 (hζe ▸ hζ')
  obtain ⟨Q, φ, hQ⟩ := exists_isPolFibre hB ((algebraMap F M).comp emb) P₁
  obtain ⟨Q', ψ, hQ'⟩ := exists_isPolFibre hB (algebraMap M (AlgebraicClosure M)) Q
  refine ⟨M, inferInstance, inferInstance, Q, φ, ζ, inferInstance, hMgal, hdeg, hζ, hQ.1, hQ.2.1, hQ.2.2.symm,
    LevelGalois.nonempty_level_of_rational Q K hK0 ζ hζ Q' ψ hQ' fun y hy => ?_⟩
  let σ := algebraMap M (AlgebraicClosure M)
  let τ' : L →ₐ[M] AlgebraicClosure M := IsAlgClosed.lift
  let τ : L →+* AlgebraicClosure M := τ'.toRingHom
  have hτ : spMap τ ≫ spMap (algebraMap M L) = spMap σ := by
    rw [GlobalTheory.spMap_comp_spMap]
    exact congrArg spMap (RingHom.ext τ'.commutes)
  have hML : spMap (algebraMap M L) ≫ spMap ((algebraMap F M).comp emb) = spMap ((algebraMap F L).comp emb) := by
    rw [GlobalTheory.spMap_comp_spMap]
    rfl
  have hPg : IsGrpPullback Q.A P₁.A (spMap ((algebraMap F M).comp emb)) φ := hQ.2.1
  have hQg : IsGrpPullback Q'.A Q.A (spMap σ) ψ := hQ'.2.1
  let y₀ := ObjPull.pushEquiv hPg _ (ObjPull.pushEquiv hQg (𝟙_ _) y)
  have hy₀ : y₀ ^ K = 1 := by simp only [y₀, ← map_pow, hy, map_one]
  let j : Over.mk ((Over.mk (spMap τ)).hom ≫ spMap ((algebraMap F L).comp emb)) ⟶
      Over.mk (((𝟙_ (Over (Sp (AlgebraicClosure M)))).hom ≫ spMap σ) ≫ spMap ((algebraMap F M).comp emb)) :=
    Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ (𝟙 _ ≫ spMap σ) ≫ _ = spMap τ ≫ _
      rw [Category.id_comp, Category.id_comp, ← hML, ← hτ, Category.assoc])
  let y₁ := j ≫ y₀
  have hy₁ : y₁ ^ K = 1 := by rw [← MonObj.comp_pow, hy₀, MonObj.comp_one]
  have hy₁l : y₁.left = (y.left ≫ ψ) ≫ φ := Category.id_comp _
  let y₂ := (ObjPull.pushEquiv h₃ (Over.mk (spMap τ))).symm y₁
  obtain ⟨a, ha⟩ := lev.span _ (spMap τ) y₂ (by rw [← map_pow, hy₁, map_one])
  rw [← GenSpread.comp_linComb] at ha
  set v := linComb lev.pt (fun i => (a i : ℕ)) with hv
  have hvl : spMap τ ≫ v.left = y₂.left := congrArg CommaMorphism.left ha
  let z : Over.mk (spMap ((algebraMap F L).comp emb)) ⟶ P₁.A := Over.homMk (v.left ≫ φ₃) (by
    rw [Category.assoc, h₃.1.w, ← Category.assoc, Over.w v]
    exact Category.id_comp _)
  let k : Over.mk ((Over.mk (spMap τ)).hom ≫ spMap ((algebraMap F L).comp emb)) ⟶
      Over.mk (spMap ((algebraMap F L).comp emb)) := Over.homMk (spMap τ) rfl
  have hzl : spMap τ ≫ z.left = y₁.left := by
    rw [← ObjPull.pushEquiv_symm_left h₃ _ y₁]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ₃) hvl)
  have hkz : k ≫ z = y₁ := Over.OverMorphism.ext hzl
  have hz : z ^ K = 1 := by
    have h : k ≫ z ^ K = k ≫ 1 := by rw [MonObj.comp_pow, hkz, hy₁, MonObj.comp_one]
    exact Over.OverMorphism.ext (spec_map_field_cancel τ _ _ (congrArg CommaMorphism.left h))
  obtain ⟨w, hw⟩ := hpts z hz
  have hw2 : w ≫ P₁.A.hom = 𝟙 _ ≫ spMap ((algebraMap F M).comp emb) := by
    refine spec_map_field_cancel (algebraMap M L) _ _ ?_
    rw [← Category.assoc, hw, Over.w z, Category.id_comp, hML]
    rfl
  let x : 𝟙_ (Over (Sp M)) ⟶ Q.A := Over.homMk (hPg.1.lift w (𝟙 _) hw2) (hPg.1.lift_snd _ _ _)
  have hxl : x.left ≫ φ = w := hPg.1.lift_fst _ _ _
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  refine hQg.1.hom_ext ?_ ?_
  · rw [ObjPull.secPull_left]
    refine hPg.1.hom_ext ?_ ?_
    · rw [Category.assoc, hxl, ← hy₁l, ← hzl, ← hw, ← Category.assoc, hτ]
    · rw [Category.assoc, Over.w x, Category.assoc, hQg.1.w, ← Category.assoc, Over.w y]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [Over.w, Over.w]

end GlobalTheory.LevelPrimePower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupPrimePowerLevelRegularChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem exists_setup_regAt_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ev ∧ RegAt X₁ z₁ ev ∧ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧ Refines Q ρ D₀.toPre e₀ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsym hnn hpos hmono ξ hU l hl hln j₀
  obtain ⟨j, Y, q, hj, hqf, hqs, hB⟩ := GlobalTheory.T.exists_thetaSetup_levelCover_every_point g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth l hl hln j₀
  obtain ⟨V₁, _, _, _, ρ, D₀, e₀, y, y', hcn, hinj, hfin, href, hy, hy'⟩ :=
    GlobalTheory.T.exists_refined_degenerationData_finiteExtension_lift g n F Z i W hW V Q m t δ hrk ht hsym hnn hpos hmono ξ hU Y q hqf hqs
  obtain ⟨X₁, yM, hrN, hyM, hreg⟩ := hB (FractionRing V₁) y'
  obtain ⟨z₁, ev, hloc, he1, he2⟩ := GlobalTheory.T.exists_stalk_lift_finite_cover_normal_local V₁ hcn.2.1 X₁.M.Z Z X₁.π X₁.fin (spMap ρ ≫ ξ) yM
    (by rw [hyM, ← Category.assoc, hy', hy])
  refine ⟨j, X₁, z₁, V₁, inferInstance, inferInstance, inferInstance, ρ, ev, D₀, e₀, hj, hrN, hcn, hinj, hfin, hloc, ?_, he1,
    href⟩
  intro a ha
  rw [he2]
  exact hreg a ha

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitFiniteExtensionClassicalPointFactors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TraitExtLab

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp S.R ⟶ F.X) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → ∃ (T' : Trait F) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : S.R →+* FractionRing T'.V) (e : T'.D.toPre.X ≃+ T.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₀ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.β a b = k * T.β (e a) (e b) := by
  intro g n F o Ω _ _ _ _ S u' p _ y₀ T ι hι hy
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  have hQ := GlobalTheory.T.padic_mem_range_complete_dvr_padicAlgCl p T.V T.complete ι hι
  obtain ⟨W, _, _, _, hWc, _, fV, fK, κ, hfV, hfVl, -, hfK, hκι, hκ, hy₀⟩ :=
    GlobalTheory.T.exists_finite_extension_complete_dvr_padicAlgCl p T.V T.complete ι hι hQ S.R y₀
  have hbase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T', f, gK, hf, hfl, hff, hgK, hTy⟩ :=
    traitExtSt g n _ (zetaAway n) F W hbase inferInstance (spMap fK ≫ T.y)
  letI : Algebra (FractionRing W) (FractionRing T'.V) := gK.toAlgebra
  letI : Algebra W T'.V := f.toAlgebra
  haveI : Module.Finite W T'.V := hff
  haveI : Algebra.IsIntegral W T'.V := Algebra.IsIntegral.of_finite W T'.V
  haveI : IsLocalHom (algebraMap W T'.V) := hfl
  have hcomp : (algebraMap (FractionRing W) (FractionRing T'.V)).comp (algebraMap W (FractionRing W)) =
      (algebraMap T'.V (FractionRing T'.V)).comp (algebraMap W T'.V) := RingHom.ext hgK
  have hI : ∀ a : T'.V, _root_.IsIntegral (FractionRing W) (algebraMap T'.V (FractionRing T'.V) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap W (FractionRing W)) (algebraMap T'.V (FractionRing T'.V)) hcomp
      (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing W) (FractionRing T'.V) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := T'.V) x
    rw [div_eq_mul_inv]
    exact (hI a).isAlgebraic.mul (hI b).isAlgebraic.inv⟩
  letI : Algebra (FractionRing W) (PadicAlgCl p) := κ.toAlgebra
  let ιA : FractionRing T'.V →ₐ[FractionRing W] PadicAlgCl p := IsAlgClosed.lift
  let ι' : FractionRing T'.V →+* PadicAlgCl p := ιA
  have hι'κ : ι'.comp gK = κ := ιA.comp_algebraMap
  have hint := GlobalTheory.unitBall_eq_of_integral_dvr p W T'.V hf κ ι' (fun v => by
    show ι' (algebraMap T'.V (FractionRing T'.V) (f v)) = _
    rw [← hgK]
    exact congrArg (fun h : FractionRing W →+* PadicAlgCl p => h (algebraMap W (FractionRing W) v)) hι'κ) hκ
  have hιc : ι'.comp (gK.comp fK) = ι := by rw [← RingHom.comp_assoc, hι'κ, hκι]

  have hr : ∀ a, y₀ a ∈ ι'.range := fun a => by
    obtain ⟨x, hx⟩ := hy₀ a
    exact ⟨gK x, by rw [← hx, ← hι'κ]; rfl⟩
  let eι : FractionRing T'.V ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict
    ⟨fun a b hab => ι'.injective (congrArg Subtype.val hab), ι'.rangeRestrict_surjective⟩
  let yK : S.R →+* FractionRing T'.V := eι.symm.toRingHom.comp (y₀.codRestrict ι'.range hr)
  have hyK : ι'.comp yK = y₀ := RingHom.ext fun a =>
    congrArg Subtype.val (eι.apply_symm_apply (y₀.codRestrict ι'.range hr a))

  have hne : f (fV T.ϖ) ≠ 0 := fun h => T.irr.ne_zero (hfV (hf (by rw [h, map_zero, map_zero])))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T'.irr
  have hbase' : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  haveI : IsLocalHom (f.comp fV) := by
    haveI : IsLocalHom f := hfl
    haveI : IsLocalHom fV := hfVl
    exact RingHom.isLocalHom_comp f fV
  obtain ⟨e₀, he₀⟩ := TraitUniq.traitUniq g n _ (zetaAway n) F T T' T'.V (f.comp fV) (RingHom.id _) (gK.comp fK)
    (RingHom.id _) hbase' inferInstance (hf.comp hfV) Function.injective_id inferInstance inferInstance
    (fun a => by simp only [RingHom.comp_apply, hfK, hgK]) (fun a => rfl)
    (by rw [hTy, spMap_comp', Category.assoc]; rw [show spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ from Spec.map_id _, Category.id_comp])
    T'.ϖ m 1 T'.irr hm (by rw [pow_one, RingHom.id_apply])
  refine ⟨T', ι', yK, e₀.symm, m, hint, hyK, ?_, ?_, ?_⟩
  · haveI : Epi (spMap ι') := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (spMap ι'), ← Category.assoc, ← spMap_comp', hyK, hy, hTy, ← hιc, spMap_comp', spMap_comp',
      Category.assoc, Category.assoc]
  · obtain ⟨u, hu⟩ := hm
    have hunit : ∀ w : T'.Vˣ, ‖ι' (algebraMap T'.V _ (w : T'.V))‖ = 1 := fun w => by
      have h1 := (hint _).2 ⟨(w : T'.V), rfl⟩
      have h2 := (hint _).2 ⟨((w⁻¹ : T'.Vˣ) : T'.V), rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (w : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (w : T'.V))),
        norm_nonneg (ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V)))]
    have e1 : ι (algebraMap T.V _ T.ϖ) = ι' (algebraMap T'.V _ (f (fV T.ϖ))) := by
      rw [← hιc, RingHom.comp_apply, RingHom.comp_apply, hfK, hgK]
    have e2 : f (fV T.ϖ) = T'.ϖ ^ m * ((u⁻¹ : T'.Vˣ) : T'.V) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e1, e2, map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]
  · intro a b
    have h := he₀ (e₀.symm a) (e₀.symm b)
    simp only [AddEquiv.apply_symm_apply, Nat.cast_one, one_mul] at h
    exact h.symm

end GlobalTheory.TraitExtLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.GenTrait

theorem spMap_stalkHom_fromSpecStalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)
    (x : M.Z) : spMap (M.stalkHom x) ≫ M.Z.fromSpecStalk x = M.pt := by
  have e2 : spMap (M.stalkHom x) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
      Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) x)) := by
    rw [RatModel.stalkHom]
    show Spec.map _ = _
    rw [CommRingCat.ofHom_hom, Spec.map_comp]
    rfl
  rw [e2, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt

end GlobalTheory.Poinc.GenTrait

open GlobalTheory.Poinc.GenTrait in

theorem GlobalTheory.Poinc.exists_trait_of_stalk_dvr : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ F.X) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : Trait F) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  intro g n o _ ζ F o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ
  haveI : CharZero (M.Z.presheaf.stalk x) := (M.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.Poinc.traitExtSt g n o ζ F V hB inferInstance (spMap γ₀ ≫ y₀)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e, ← Formalism.L2.Pj.spMap_comp',
      Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePreconnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ZariskiConn

theorem fibre_preconnected : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ z : Z, _root_.IsPreconnected (π.base ⁻¹' {z}) := by
  intro Y Z π _ _ _ _ hN U hU hiso z
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  have hS := GlobalTheory.T.bijective_sections_preimage_affine_proper_birational Y Z π hN U hU hiso V hV
  haveI : IsAffine (V : Scheme) := hV
  have hC := GlobalTheory.T.zariskiConnectedness_isPreconnected_fibre_affine (V : Scheme) (π ⁻¹ᵁ V) (π ∣_ V) hS ⟨z, hzV⟩
  have key : π.base ⁻¹' {z} = (π ⁻¹ᵁ V).ι.base '' ((π ∣_ V).base ⁻¹' {⟨z, hzV⟩}) := by
    ext y
    constructor
    · intro hy
      have hy' : π.base y = z := hy
      have hyV : y ∈ π ⁻¹ᵁ V := by
        show π.base y ∈ V
        rw [hy']; exact hzV
      refine ⟨⟨y, hyV⟩, ?_, rfl⟩
      show (π ∣_ V).base ⟨y, hyV⟩ = ⟨z, hzV⟩
      exact Subtype.ext ((morphismRestrict_base_coe π V ⟨y, hyV⟩).trans hy')
    · rintro ⟨w, hw, rfl⟩
      have hw' : (π ∣_ V).base w = ⟨z, hzV⟩ := hw
      exact (morphismRestrict_base_coe π V w).symm.trans (congrArg Subtype.val hw')
  rw [key]
  exact hC.image _ (π ⁻¹ᵁ V).ι.base.hom.continuous.continuousOn

end GlobalTheory.ZariskiConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosedStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ x : Root m, DbarCoh (atlas X σ) (grF E H x) (grF E H x) := by
  first | exact @GlobalTheory.ChernCalc.GradedForm.dbarCoh_grF | exact GlobalTheory.ChernCalc.GradedForm.dbarCoh_grF | (intros; apply GlobalTheory.ChernCalc.GradedForm.dbarCoh_grF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAddStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasKernelOrderPPowerDegree_comp_le_add : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ), HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  first | exact @GlobalTheory.Dieu.hasLogDeg_comp_le | exact GlobalTheory.Dieu.hasLogDeg_comp_le | (intros; apply GlobalTheory.Dieu.hasLogDeg_comp_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFieldPointStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_fieldPoint : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → ∀ (K : Type) [Field K] (s : Sp K ⟶ S), HasRep A g (Over.mk s) := by
  first | exact @GlobalTheory.DualCon.FieldRep.hasRep_field | exact GlobalTheory.DualCon.FieldRep.hasRep_field | (intros; apply GlobalTheory.DualCon.FieldRep.hasRep_field <;> assumption)
end

